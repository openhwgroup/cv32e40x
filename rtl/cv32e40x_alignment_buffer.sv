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

  output logic           busy_o,

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

  // Store number of resps to flush when get get a branch
  logic [1:0] n_flush_n, n_flush_q, n_flush_fsm;

  // Fetch valid gated while flushing
  logic fetch_valid;

  assign fetch_valid = (n_flush_q > 0) ? 1'b0 : fetch_valid_i;

  // For any number > 0, subtract 1 if we also issue to if_stage
  // If we don't have any incoming but issue to if_stage, signal 3 as negative 1 (pop)
  assign n_pushed_ins = (instr_valid_o & instr_ready_i) ? 
                        (n_incoming_ins >0) ? n_incoming_ins - 1 : 2'b11 :
                        n_incoming_ins;

  // Request a transfer if FSM asks for it, or we do a branch
  assign trans_req_o = trans_req_fsm || branch_i;

  // Busy if we expect any responses, or we have an active trans_req_o
  assign busy_o = (aligner_cs inside {I0_10, I0_11, I1_10, I2_10}) || trans_req_o;

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
  assign valid = valid_q[0] || fetch_valid;

  // Unaligned instructions will either be split across index 0 and 1, or index 0 and incoming data
  assign rdata_unaligned = (valid_q[1]) ? {rdata_q[1][15:0], rdata[31:16]} : {fetch_rdata_i[15:0], rdata[31:16]};

  // Unaligned instructions are valid if index 1 is valid (index 0 will always be valid if 1 is)
  // or if we have data in index 0 AND we get a new incoming instruction
  assign valid_unaligned = (valid_q[1] || (valid_q[0] && fetch_valid));

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
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    rdata_int   = rdata_q;
    valid_int   = valid_q;

    // Loop through indices and store incoming data to first available slot
    if (fetch_valid) begin
      for(int j = 0; j < DEPTH; j++) begin
        if (!valid_q[j]) begin
          rdata_int[j] = fetch_rdata_i;
          valid_int[j] = 1'b1;

          break;
        end // valid_q[j]
      end // for loop
    end // fetch_valid
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
    // Default values
    aligner_ns = aligner_cs;
    trans_req_fsm = 1'b0;
    n_flush_fsm = 2'b00;

    unique case (aligner_cs)
        I0_00: begin // 0 in FIFO, 0 incoming
          // FETCH
          trans_req_fsm = 1'b1;

          // Handle brances
          if(branch_i) begin
            // We get an immediate ack
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            // Stay in this state until we get an ack
            // This state will keep trans_req_o high 
            // Even though branch_i goes low
            end else begin
              aligner_ns = I0_00;
            end
            
            // Could be flushing from before, keep value from n_flush_q
            n_flush_fsm = n_flush_q;
            
          end else begin
            // No branch and no instructions in FIFO
            // only proceed if we get an ack
            if(trans_req_fsm && trans_ack_i) begin
              aligner_ns = I0_10;
            end
          end
        end
        I0_10: begin // 0 in FIFO, 1 incoming (this cycle)
          // FETCH
          trans_req_fsm = 1'b1;

          // On a branch, we're clearing the fifo
          if(branch_i) begin
            if(trans_ack_i) begin
              // Immediate ack, expect response
              aligner_ns = I0_10;
            end else begin
              // No ack, go to I0_00 which expects not response
              // I0_00 will keep trans_req_o high
              aligner_ns = I0_00;
            end

            // Calculate how much we need to flush of incoming responses

            if(fetch_valid_i == 1'b0) begin
              if(n_flush_q == 2'b00) begin
                // Nothing to flush from previous cycle(s)
                // No incoming data, 1 resp to flush
                n_flush_fsm = 2'b01;
              end else begin
                // We are already flushing, don't override value
                // but add the 1 expected resp for this state
                n_flush_fsm = n_flush_q + 2'b01;
              end
            end else begin
              // We have incoming data, nothing to add
              // Keep n_flush_q as we can be flushing from earlier branches
              n_flush_fsm = n_flush_q;
            end
          end else begin
            // No branch, and transfer is ack'ed
            if(trans_req_fsm && trans_ack_i) begin
              // Next state depends on how many instructions are pushed to the fifo
              case (n_pushed_ins)              
                2'd0 : begin
                  if(fetch_valid) begin
                    // Data directly consumed, stay in this state
                    aligner_ns = I0_10;
                  end else begin
                    // No valid resp, expect two outstanding responses
                    aligner_ns = I0_11;
                  end
                end
                2'd1: begin
                    // Push one instructions to FIFO
                    // Expect one outstanding response
                    aligner_ns = I1_10;
                end
                2'd2: begin
                    // Push two instructions to FIFO
                    // Expect one outstanding response
                    aligner_ns = I2_10;
                end
                default: begin
                  // Should not end up here
                  // as 2'd3 would imply popped insn, and 
                  // we don't have any in the FIFO for this state
                end
              endcase
              
            end else begin
              // trans not acked, no extra outstanding from this cycle
              case (n_pushed_ins)              
                2'd0 : begin
                  if(fetch_valid) begin
                    // Data directly consumed, no outstanding resps left
                    aligner_ns = I0_00;
                  end else begin
                    // No incoming data, still one outstanding left
                    aligner_ns = I0_10;
                  end
                end
                2'd1: begin
                    // We push one ins from resp, no outstanding left
                    aligner_ns = I1_00;
                end
                2'd2: begin
                    // We push two ins from resp, no outstanding left
                    aligner_ns = I2_00;
                end
                default: begin
                  // Should not end up here
                  // as 2'd3 would imply popped insn, and 
                  // we don't have any in the FIFO for this state
                end
              endcase
            end
          end
        end
        I0_11: begin // 0 in FIFO, 2 incoming (this and next cycle)
          /////////////////////
          if(branch_i) begin
            if(trans_ack_i) begin
              // Acked, expect one resp
              aligner_ns = I0_10;
            end else begin
              // Not acked, expect 0 resps
              // I0_00 will keep trans_req_o high
              aligner_ns = I0_00;
            end

            if(fetch_valid_i) begin
              // 1 resp to flush plus any from earlier flushes
              n_flush_fsm = n_flush_q + 2'b01;
            end else begin
              // 2 resps to flush + any from earlier flushes
              n_flush_fsm = n_flush_q + 2'b10;
            end
          end else begin
            case (n_pushed_ins)              
              2'd0 : begin
                  if(fetch_valid) begin
                    // Data directly consumed, one resp left
                    aligner_ns = I0_10;
                  end else begin
                    // No resps, two outstanding left
                    aligner_ns = I0_11;
                  end
              end
              2'd1: begin
                  // One outstanding left
                  aligner_ns = I1_10;
              end
              2'd2: begin
                  // One outstanding left
                  aligner_ns = I2_10;
              end
              default: begin
                // Should not end up here
                // as 2'd3 would imply popped insn, and 
                // we don't have any in the FIFO for this state
              end
            endcase
          end
          
        end
        I1_00: begin // 1 in FIFO, 0 incoming
          // FETCH
          trans_req_fsm = 1'b1;
          
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end
            // No resps to flush from this state, 
            // but we could be flushing from before
            n_flush_fsm = n_flush_q;
          end else begin
            // Transfer is ack'ed
            if(trans_req_fsm && trans_ack_i) begin
              // Next state
              case (n_pushed_ins)              
                2'd0 : begin
                    // Still one ins in FIFO, expect one resp
                    aligner_ns = I1_10;
                end
                2'd3: begin
                    // We pop one, expect one resp
                    aligner_ns = I0_10;
                end
                default: begin
                  // Should not end up here as we expect no responses
                end
              endcase
              
            end else begin
              // No ack, but we may have been popped
              case (n_pushed_ins)              
                2'd0 : begin
                    aligner_ns = I1_00; // We keep in the same state
                end
                2'd3: begin
                    // We pop one
                    aligner_ns = I0_00; 
                end
                default: begin
                  // Should not end up here as we expect no responses
                end
              endcase
            end
          end
          
        end
        I1_10: begin // 1 in FIFO, 1 incoming (this cycle)
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end

            // Calculat how many words to flush
            if(!fetch_valid_i) begin
              // 1 resp to flush 
              n_flush_fsm = n_flush_q + 2'b01;
            end else begin
              n_flush_fsm = n_flush_q;
            end
          end else begin
            case (n_pushed_ins)              
              2'd0 : begin
                  if(fetch_valid) begin
                  // Directly consumed, no extra resps
                    aligner_ns = I1_00;
                  end else begin
                    // Nothing pushed, still expect one resp
                    aligner_ns = I1_10;
                  end
              end
              2'd1: begin
                  // One ins pushed, expect no more responses
                  aligner_ns = I2_00;
              end
              2'd2: begin
                  // Two ins pushed, expect no more responses
                  aligner_ns = I3_00;
              end
              2'd3: begin
                  // We pop one
                  // Implies no response, expect one resp
                  aligner_ns = I0_10;
              end
            endcase
          end
        end
        I2_00: begin // 2 in FIFO, 0 incoming
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end
            // No need to calculate number of words to flush
            // There is no outstanding response, and we can't
            // reach this state until after previous flushes are done
          end else begin
            if(instr_valid_o && instr_ready_i) begin
              // One instruction left, no expected responses
              aligner_ns = I1_00;
            end
          end
        end
        I2_10: begin // 2 in FIFO, 1 incoming (this cycle)
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end
            // Number of words to flush
            // There is one outstanding response, and we can't
            // reach this state until after previous flushes are done
            if(!fetch_valid_i) begin
              // 1 resp to flush
              n_flush_fsm = 2'b01;
            end else begin
              n_flush_fsm = 2'b00;
            end
          end else begin
            case (n_pushed_ins)              
              2'd0 : begin
                  if(fetch_valid) begin
                    // No ins pushed, expect no responses
                    // We could receive one ins and send out one ins 
                    aligner_ns = I2_00;
                  end else begin
                    // Nothing incoming, stay in this state
                    aligner_ns = I2_10;
                  end
              end
              2'd1: begin
                  // One ins pushed, expect no resps
                  aligner_ns = I3_00;
              end
              2'd2: begin
                  // Two ins pushed, expect no resps
                  aligner_ns = I4_00;
              end
              2'd3: begin
                  // One ins popped
                  // Implies no resp, so we still expect one response
                  aligner_ns = I1_10;
              end
            endcase
          end
        end
        I3_00: begin // 3 in FIFO, 0 incoming
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end
            // No need to calculate flush as we have no 
            // expected resps.
          end else begin
            // If we have a valid output, we've got two insn left in FIFO
            if(instr_valid_o && instr_ready_i) begin
              aligner_ns = I2_00;
            end
        end
        end
        I4_00: begin // 4 in FIFO, 0 incoming
          if(branch_i) begin
            if(trans_ack_i) begin
              aligner_ns = I0_10;
            end else begin
              aligner_ns = I0_00;
            end
            // No need to calculate flush as we have no 
            // expected resps.
          end else begin
            // If we have a valid output, we've got three insn left in FIFO
            if(instr_valid_o && instr_ready_i) begin
              aligner_ns = I3_00;
            end
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
  // This also be done by inspecting the fifo content
  always_comb begin
    // Set default values
    aligned_n = aligned_q;
    complete_n = complete_q;
    n_incoming_ins = 2'd0;

    // On a branch we need to know if it is aligned or not
    // the complete flag will be special cased for unaligned branches
    // as aligned=0 and complete=1 can only happen in that case
    if(branch_i) begin
      aligned_n = !branch_addr_i[1];
      complete_n = branch_addr_i[1];
    end else begin
      // Valid response
      if(fetch_valid) begin
        // We are on an aligned address
        if(aligned_q) begin
          // uncompressed in rdata
          if(fetch_rdata_i[1:0] == 2'b11) begin
            n_incoming_ins = 2'd1;
            // Still aligned and complete, no need to update
          end else begin
            // compressed in lower part, check next halfword
            if(fetch_rdata_i[17:16] == 2'b11) begin
              // Upper half is uncompressed, not complete
              // 1 complete insn
              n_incoming_ins = 2'd1;
              // Not aligned nor complete, as upper 16 bits are uncompressed
              aligned_n = 1'b0;
              complete_n = 1'b0;
            end else begin
              // Another compressed in upper half
              // two complete insn in word, still aligned and complete
              n_incoming_ins = 2'd2;
              aligned_n = 1'b1;
              complete_n = 1'b1;
            end
          end
        // We are on ann unaligned address
        end else begin
          // Unaligned and complete_q==1 can only happen
          // for unaligned branches, signalling that lower
          // 16 bits can be discarded
          if(complete_q) begin
            // Uncompressed unaligned
            if(fetch_rdata_i[17:16] == 2'b11) begin
              // No complete ins in data
              n_incoming_ins = 2'd0;
              // Still unaligned
              aligned_n = 1'b0;
              // Not a complete instruction
              complete_n = 1'b0;
            end else begin
              // Compressed unaligned
              // We have one insn in upper 16 bits
              n_incoming_ins = 2'd1;
              // We become aligned
              aligned_n = 1'b1;
              // Complete instruction
              complete_n = 1'b1;
            end
          end else begin
            // Incomplete. Check upper 16 bits for content
            // Implied that lower 16 bits contain the MSBs
            // of an uncompressed instruction
            if(fetch_rdata_i[17:16] == 2'b11) begin
              // Upper 16 is uncompressed
              // 1 complete insn in word
              n_incoming_ins = 2'd1;
              // Unaligned and not complete
              aligned_n = 1'b0;
              complete_n = 1'b0;
            end else begin
              // Compressed unaligned
              // Two complete insn in word
              // Aligned and complete
              n_incoming_ins = 2'd2;
              aligned_n = 1'b1;
              complete_n = 1'b1;
            end // rdata[17:16]
          end // complete_q
        end // aligned_q
      end // fetch_valid
    end // branch
  end // comb


  // number of resps to flush
  always_comb
  begin
    // Default value
    n_flush_n = n_flush_q;

    // On a branch, the FSM will calculate
    // the number of words to flush
    if(branch_i) begin
      n_flush_n = n_flush_fsm;
    end else begin
      // Decrement flush counter on valid inputs
      if(fetch_valid_i && (n_flush_q > 0)) begin
        n_flush_n = n_flush_q - 2'b01;
      end
    end
  end
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
      n_flush_q <= 'd0;
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
      n_flush_q <= n_flush_n;
      
    end
  end

  // Output instruction address to if_stage
  assign instr_addr_o      = addr_q;

 
  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON
  logic [2:0] outstanding_cnt;
  logic [2:0] next_outstanding_cnt;
  logic count_up;
  logic count_down;
  assign count_up   = trans_req_o && trans_ack_i;     // Increment upon accepted transfer request
  assign count_down = fetch_valid_i;                       // Decrement upon accepted transfer response

  always_comb begin
    case ({count_up, count_down})
      2'b00  : begin
        next_outstanding_cnt = outstanding_cnt;
      end
      2'b01  : begin
        next_outstanding_cnt = outstanding_cnt - 1'b1;
      end
      2'b10  : begin
        next_outstanding_cnt = outstanding_cnt + 1'b1;
      end
      2'b11  : begin
        next_outstanding_cnt = outstanding_cnt;
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
     outstanding_cnt <= 'd0;
    end 
    else
    begin
     outstanding_cnt <= next_outstanding_cnt;
    end
  end

  // No resp in states which not expect it
  assert property (
    @(posedge clk) (aligner_cs == I0_00) |-> (fetch_valid == 1'b0) );
  assert property (
    @(posedge clk) (aligner_cs == I1_00) |-> (fetch_valid == 1'b0) );
  assert property (
    @(posedge clk) (aligner_cs == I2_00) |-> (fetch_valid == 1'b0) );
  assert property (
    @(posedge clk) (aligner_cs == I3_00) |-> (fetch_valid == 1'b0) );
  assert property (
    @(posedge clk) (aligner_cs == I4_00) |-> (fetch_valid == 1'b0) );

  assert property (
    @(posedge clk) (aligner_cs == I0_00) |-> (outstanding_cnt - n_flush_q == 'd0) );
  assert property (
    @(posedge clk) (aligner_cs == I1_00) |-> (outstanding_cnt - n_flush_q == 'd0) );
  assert property (
    @(posedge clk) (aligner_cs == I2_00) |-> (outstanding_cnt - n_flush_q == 'd0) );
  assert property (
    @(posedge clk) (aligner_cs == I3_00) |-> (outstanding_cnt - n_flush_q == 'd0) );
  assert property (
    @(posedge clk) (aligner_cs == I4_00) |-> (outstanding_cnt - n_flush_q == 'd0) );

   
`endif

endmodule
