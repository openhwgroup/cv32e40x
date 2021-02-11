// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Pasquale Davide Schiavone - pschiavo@iis.ee.ethz.ch        //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@greenwaves-technologies.com            //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Instrctuon Aligner                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_alignment_buffer import cv32e40x_pkg::*;
#(
  parameter DEPTH = 3,                           // Prefetch FIFO Depth
  parameter FIFO_ADDR_DEPTH = 2 
)
(
  input  logic           clk,
  input  logic           rst_n,

  // Interface to prefetch_controller
  input  logic           fetch_valid_i,
  input  logic [31:0]    fetch_rdata_i,
  output logic           trans_req_o,
  input  logic           trans_ack_i,


  
  // Interface to if_stage
  output logic           instr_valid_o,
  input  logic           instr_ready_i,
  output logic [31:0]    instr_aligned_o,
  output logic [31:0]    instr_addr_o,

  // Branch control
  input  logic [31:0]    branch_addr_i,
  input  logic           branch_i         // Asserted if we are branching/jumping now

  
);

  
  logic [31:0]       pc_q;
  
  // FSM
  alignment_state_e aligner_cs, aligner_ns;

  logic trans_req_fsm;

  // number of instructions in resp_data
  logic [1:0] n_incoming_ins;

  // Number of instructions pushed to fifo
  logic [1:0] n_pushed_ins;

  logic aligned_n, aligned_q;
  logic complete_n, complete_q;

  // For any number > 0, subtract 1 if we also issue to if_stage
  // If we don't have any incoming but issue to if_stage, signal 3 as negative 1 (pop)
  assign n_pushed_ins = (instr_valid_o & instr_ready_i) ? 
                        (n_incoming_ins >0) ? n_incoming_ins - 1 : 2'b11 :
                        n_incoming_ins;

  assign trans_req_o = trans_req_fsm || branch_i;
  
  //////////////////
  // FIFO signals //
  //////////////////
  // index 0 is used for output
  logic [0:DEPTH-1] [31:0]  rdata_n,   rdata_int,   rdata_q;
  logic [0:DEPTH-1]         valid_n,   valid_int,   valid_q;

  logic             [31:0]  addr_n, addr_q, addr_incr;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;

  // Aligned instructions will either be fully in index 0 or incoming data
  assign rdata = (valid_q[0]) ? rdata_q[0] : fetch_rdata_i;
  
  // Aligned instructions are valid if we have one in index0, or using from incoming interface
  assign valid = valid_q[0] || fetch_valid_i;

  // Unaligned instructions will either be split across index 0 and 1, or index 0 and incoming data
  assign rdata_unaligned = (valid_q[1]) ? {rdata_q[1][15:0], rdata[31:16]} : {fetch_rdata_i[15:0], rdata[31:16]};

  // Unaligned instructions are valid if index 1 is valid (index 0 will always be valid if 1 is)
  // or if we have data in index 0 AND we get a new incoming instruction
  assign valid_unaligned = (valid_q[1] || (valid_q[0] && fetch_valid_i));

  // unaligned_is_compressed and aligned_is_compressed are only defined when valid = 1 (which implies that instr_valid_o will be 1)
  assign unaligned_is_compressed = rdata[17:16] != 2'b11;
  assign aligned_is_compressed   = rdata[1:0] != 2'b11;


  // Output instructions to the if stage
  always_comb
  begin
    instr_aligned_o = rdata;

    // Invalidate output if we get a branch
    if (branch_i) begin
      instr_valid_o = 1'b0;
    end else if (instr_addr_o[1]) begin
      // unaligned instruction
      instr_aligned_o = rdata_unaligned;

      // No instruction valid
      if (!valid) begin
        instr_valid_o = valid;
      // Unaligned instruction is compressed, we only need 16 upper bits from index 0
      end else if (unaligned_is_compressed) begin
        instr_valid_o = valid;
      end else begin
      // Unaligned is not compressed, we need data form either index 0 and 1, or 0 and input
        instr_valid_o = valid_unaligned;
      end
    end else begin
      // aligned case, contained in index 0
      instr_aligned_o = rdata;
      instr_valid_o = valid;
    end
  end
  
  //////////////////////////////////////////////////////////////////////////////
  // input port
  //////////////////////////////////////////////////////////////////////////////

  // Indicate FIFO fill count. On a branch (branch_i) the FIFO will be cleared
  // on the next clock edge. Ahead of that the FIFO is indicated to be empty 
  // so that a new transaction request in response to a branch are always
  // requested as soon as possible.
/*
  always_comb
  begin
      fifo_cnt_o = 'd0;
      // Loop through valid's and store count
      for(int i=0;i<DEPTH;i++) begin : fifo_cnt_loop
        if( valid_q[i]) begin
            fifo_cnt_o = DEPTH'(i)+1;
        end
      end

      // In case of branch, we flush and set cnt to 0
      if( branch_i) begin
          fifo_cnt_o = 'd0;
      end
  end // always_comb
*/  

  //////////////////////////////////////////////////////////////////////////////
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    rdata_int   = rdata_q;
    valid_int   = valid_q;

    // Loop through indices and store incoming data to first available slot
    if (fetch_valid_i) begin
      for(int j = 0; j < DEPTH; j++) begin
        if (!valid_q[j]) begin
          rdata_int[j] = fetch_rdata_i;
          valid_int[j] = 1'b1;

          break;
        end // valid_q[j]
      end // for loop
    end // fetch_valid_i
  end // always_comb

  // Calculate address increment
  assign addr_incr = {addr_q[31:2], 2'b00} + 32'h4;

  // move everything by one step
  always_comb
  begin
    addr_n     = addr_q;
    rdata_n    = rdata_int;
    valid_n    = valid_int;

    // Valid instruction output
    if (instr_ready_i && instr_valid_o) begin
      if (addr_q[1]) begin
        // unaligned case
        // Set next address based on instr being compressed or not
        if (unaligned_is_compressed) begin
          addr_n = {addr_incr[31:2], 2'b00};
        end else begin
          addr_n = {addr_incr[31:2], 2'b10};
        end

        // Adcance FIFO one step
        // Unaligned will always invalidate index 0
        for (int i = 0; i < DEPTH - 1; i++)
        begin
          rdata_n[i] = rdata_int[i + 1];
        end
        valid_n = {valid_int[1:DEPTH-1], 1'b0};
      end else begin
        // aligned case
        if (aligned_is_compressed) begin
          // just increase address, do not move to next entry in FIFO
          addr_n = {addr_q[31:2], 2'b10};
        end else begin
          // move to next entry in FIFO
          // Uncompressed instruction, use addr_incr without offset
          addr_n = {addr_incr[31:2], 2'b00};

          // Advance FIFO one step
          for (int i = 0; i < DEPTH - 1; i++)
          begin
            rdata_n[i] = rdata_int[i + 1];
          end
          valid_n = {valid_int[1:DEPTH-1], 1'b0};
        end
      end
    end
  end

  // FSM comb block
  always_comb
  begin
    aligner_ns = aligner_cs;
    trans_req_fsm = 1'b0;

    unique case (aligner_cs)
        I0_00: begin // 0 in FIFO, 0 incoming
          // FETCH
          trans_req_fsm = 1'b1;
          if(trans_req_fsm && trans_ack_i) begin
            aligner_ns = I0_10;
          end
        end
        I0_10: begin // 0 in FIFO, 1 incoming (this cycle)
          // FETCH
          trans_req_fsm = 1'b1;

          // Transfer is ack'ed
          if(trans_req_fsm && trans_ack_i) begin
            // Next state depends on how many instructions are pushed to the fifo
            case (n_pushed_ins)              
              2'd0 : begin
                  aligner_ns = I0_10;
              end
              2'd1: begin
                  aligner_ns = I1_10;
              end
              2'd2: begin
                  aligner_ns = I2_10;
              end
            endcase
            // On a branch, we're clearing the fifo
            if(branch_i) begin
              aligner_ns = I0_10;
            end

          // transfer not yet accepted
          end else begin
            case (n_pushed_ins)              
              2'd0 : begin
                  aligner_ns = I0_00;
              end
              2'd1: begin
                  aligner_ns = I1_00;
              end
              2'd2: begin
                  aligner_ns = I2_00;
                  //trans_req_o = 1'b0; // No need to prefetch anyway ! NB not allowed as it is using rdata as input
              end
            endcase
          end
        end
        I0_11: begin // 0 in FIFO, 2 incoming (this and next cycle)
          /////////////////////
        end
        I1_00: begin // 1 in FIFO, 0 incoming
          // FETCH
          trans_req_fsm = 1'b1;
          
          // Transfer is ack'ed
          if(trans_req_fsm && trans_ack_i) begin
            // Next state depends on how many instructions are pushed to the fifo
            case (n_pushed_ins)              
              2'd0 : begin
                  aligner_ns = I1_10;
              end
              2'd1: begin
                  aligner_ns = I2_10;
              end
              2'd2: begin
                  aligner_ns = I3_00; //!! would require I3_10, which is not defined
              end
              2'd3: begin
                  // We pop one
                  aligner_ns = I0_10;
              end
            endcase
          // transfer not yet accepted
          end else begin
            case (n_pushed_ins)              
              2'd0 : begin
                  aligner_ns = I1_00;
              end
              2'd1: begin
                  aligner_ns = I2_00;
              end
              2'd2: begin
                  aligner_ns = I3_00;
              end
              2'd3: begin
                  // We pop one
                  aligner_ns = I0_00;
              end
            endcase
          end
          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
        I1_10: begin // 1 in FIFO, 1 incoming (this cycle)
          case (n_pushed_ins)              
            2'd0 : begin
                aligner_ns = I1_00;
            end
            2'd1: begin
                aligner_ns = I2_00;
            end
            2'd2: begin
                aligner_ns = I3_00;
            end
            2'd3: begin
                // We pop one
                aligner_ns = I0_00; // Not likely to happen
            end
          endcase
          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
        I2_00: begin // 2 in FIFO, 0 incoming
          if(instr_valid_o && instr_ready_i) begin
            aligner_ns = I1_00;
          end
          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
        I2_10: begin // 2 in FIFO, 1 incoming (this cycle)
          case (n_pushed_ins)              
            2'd0 : begin
                aligner_ns = I2_00;
            end
            2'd1: begin
                aligner_ns = I3_00;
            end
            2'd2: begin
                aligner_ns = I4_00;
            end
          endcase
          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
        I3_00: begin // 3 in FIFO, 0 incoming
          if(instr_valid_o && instr_ready_i) begin
            aligner_ns = I2_00;
          end
          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
        I4_00: begin // 4 in FIFO, 0 incoming
          if(instr_valid_o && instr_ready_i) begin
            aligner_ns = I3_00;
          end

          if(branch_i) begin
            aligner_ns = I0_10;
          end
        end
    endcase
  end // always_comb

  // FSM seq block
  always_ff @(posedge clk, negedge rst_n) begin
    if(rst_n == 1'b0) begin
      aligner_cs <= I0_00;
    end else begin
      aligner_cs <= aligner_ns;
    end // rst
  end // always_ff

  // Count number of incoming instructions in resp_data
  always_comb begin
    aligned_n = aligned_q;
    complete_n = complete_q;
    n_incoming_ins = 2'd0;
    if(branch_i) begin
      aligned_n = !branch_addr_i[1];
      complete_n = branch_addr_i[1];
    end else begin
      if(fetch_valid_i) begin
        if(aligned_q) begin
          // uncompressed
          if(fetch_rdata_i[1:0] == 2'b11) begin
            n_incoming_ins = 2'd1;
          end else begin
            // compressed, check next halfword
            if(fetch_rdata_i[17:16] == 2'b11) begin
              // uncompressed, not complete
              n_incoming_ins = 2'd1;
              aligned_n = 1'b0;
              complete_n = 1'b0;
            end else begin
              // Another compressed
              n_incoming_ins = 2'd2;
              aligned_n = 1'b1;
              complete_n = 1'b1;
            end
          end
        end else begin
          // Unaligned
          if(complete_q) begin
            // Uncompressed unaligned
            if(fetch_rdata_i[17:16] == 2'b11) begin
              n_incoming_ins = 2'd0;
              aligned_n = 1'b0;
              complete_n = 1'b0;
            end else begin
              // Compressed unaligned
              n_incoming_ins = 2'd1;
              aligned_n = 1'b1;
              complete_n = 1'b1;
            end
          end else begin
            // incomplete
            if(fetch_rdata_i[17:16] == 2'b11) begin
              n_incoming_ins = 2'd1;
              aligned_n = 1'b0;
              complete_n = 1'b0;
            end else begin
              // Compressed unaligned
              n_incoming_ins = 2'd2;
              aligned_n = 1'b1;
              complete_n = 1'b1;
            end // rdata[17:16]
          end // complete_q
        end // aligned_q
      end // fetch_valid_i
    end // branch
  end // comb

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_q    <= '0;
      rdata_q   <= '{default: '0};
      valid_q   <= '0;
      aligned_q <= 1'b0;
      complete_q <= 1'b0;
    end
    else
    begin
      aligned_q <= aligned_n;
      complete_q <= complete_n;
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (branch_i) begin
        valid_q <= '0;
        addr_q  <= branch_addr_i;       // Branch target address will correspond to first instruction received after this. 
      end else begin
        addr_q  <= addr_n;
        rdata_q <= rdata_n;
        valid_q <= valid_n;
      end
    end
  end

  // Output instruction address to if_stage
  assign instr_addr_o      = addr_q;

 
  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
/*
`ifdef CV32E40P_ASSERT_ON

  // Check for FIFO overflows
  assert property (
     @(posedge clk) (fetch_valid_i) |-> (valid_q[DEPTH-1] == 1'b0) );

  // Check that FIFO is cleared the cycle after a branch
  assert property (
     @(posedge clk) (branch_i) |=> (valid_q == 'b0) );

  // Check that FIFO is signaled empty the cycle during a branch
  //assert property (
  //   @(posedge clk) (branch_i) |-> (fifo_cnt_o == 'b0) );

  // Theck that instr_valid_o is zero when a branch is requested
  assert property (
    @(posedge clk) (branch_i) |-> (instr_valid_o == 1'b0) );
   
`endif
*/
endmodule
