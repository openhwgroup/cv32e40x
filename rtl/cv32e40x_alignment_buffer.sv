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

  input  logic           req_i,
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

  // Counter for number of instructions in the FIFO
  // FIFO_ADDR_DEPTH defines number of words
  // We must count number of instructions, thus   
  // using the value without subtracting
  logic [FIFO_ADDR_DEPTH:0] fifo_cnt_n, fifo_cnt_q;

  // Counter for number of outstanding transactions
  logic [2:0] outstanding_cnt_n, outstanding_cnt_q;

  // Number of non-flushing outstanding transactions
  logic [2:0] outstanding_nonflush_cnt;
  
  // number of complete instructions in resp_data
  logic [1:0] n_incoming_ins;

  // Number of instructions pushed to fifo
  logic [1:0] n_pushed_ins;

  // Flags to indicate aligned address and complete instructions
  logic aligned_n, aligned_q;
  logic complete_n, complete_q;

  // Store number of responses to flush when get get a branch
  logic [1:0] n_flush_n, n_flush_q, n_flush_branch;
  

  // Fetch valid gated while flushing
  logic fetch_valid;

  assign fetch_valid = (n_flush_q > 0) ? 1'b0 : fetch_valid_i;

  // For any number > 0, subtract 1 if we also issue to if_stage
  // If we don't have any incoming but issue to if_stage, signal 3 as negative 1 (pop)
  assign n_pushed_ins = (instr_valid_o & instr_ready_i) ? 
                        (n_incoming_ins >0) ? n_incoming_ins - 1 : 2'b11 :
                        n_incoming_ins;

  // Request a transfer when needed, or we do a branch
  assign trans_req_o = req_i && ((fifo_cnt_q == 'd0 && outstanding_nonflush_cnt < 3'd2) ||
                                 (fifo_cnt_q == 'd1 && outstanding_nonflush_cnt == 3'd0) ||
                                  branch_i);

  assign outstanding_nonflush_cnt = outstanding_cnt_q - n_flush_q;

  // Busy if we expect any responses, or we have an active trans_req_o
  assign busy_o = ((outstanding_cnt_q != 3'b000) && n_flush_q == 'd0) || trans_req_o;

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

  
  // Counting instructions in FIFO
  always_comb begin
    fifo_cnt_n = fifo_cnt_q;
    n_flush_branch = 2'b00;

    if(branch_i) begin
      // FIFO content is invalidated upon a branch
      fifo_cnt_n = 'd0;

      // Calculate how much to flush
      if(outstanding_nonflush_cnt > 3'b000) begin
        if(!fetch_valid_i) begin
          n_flush_branch = n_flush_q + outstanding_nonflush_cnt;
        end else begin
          n_flush_branch = n_flush_q + outstanding_nonflush_cnt - 2'b01;
        end
      end else begin
        n_flush_branch = n_flush_q;
      end
    end else begin
      // Update number of instructions when we push or pop it
      if(n_pushed_ins != 2'd0) begin
        if(n_pushed_ins == 2'b11) begin
          fifo_cnt_n = fifo_cnt_q - 1'b1;
        end else begin
          fifo_cnt_n = fifo_cnt_q + n_pushed_ins;
        end
      end  
    end
  end

  // Counting number of outstanding transactions
  // NB! This is "expected" outstanding, excluding the ones
  // that will be flushed. Set to 0 or 1 on a branch, 
  // depending on immediate accept or not
  assign outstanding_count_up   = trans_req_o && trans_ack_i;    // Increment upon accepted transfer request
  assign outstanding_count_down = fetch_valid_i;                   // Decrement upon accepted transfer response

  always_comb begin
    /*if(branch_i) begin
      // Add one if we get accepted right away
      outstanding_cnt_n = outstanding_count_up ? 2'd1 : 2'd0;
    end else begin*/
      case ({outstanding_count_up, outstanding_count_down})
        2'b00  : begin
          outstanding_cnt_n = outstanding_cnt_q;
        end
        2'b01  : begin
          outstanding_cnt_n = outstanding_cnt_q - 1'b1;
        end
        2'b10  : begin
          outstanding_cnt_n = outstanding_cnt_q + 1'b1;
        end
        2'b11  : begin
          outstanding_cnt_n = outstanding_cnt_q;
        end
      endcase
    //end
  end


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

    // On a branch, the counter logic will calculate
    // the number of words to flush
    if(branch_i) begin
      n_flush_n = n_flush_branch;
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
      fifo_cnt_q <= 'd0;
      outstanding_cnt_q <= 'd0;
    end
    else
    begin
      
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

      aligned_q <= aligned_n;
      complete_q <= complete_n;
      n_flush_q <= n_flush_n;
      fifo_cnt_q <= fifo_cnt_n;
      outstanding_cnt_q <= outstanding_cnt_n;
    end
  end

  // Output instruction address to if_stage
  assign instr_addr_o      = addr_q;

 
  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON




   
`endif

endmodule
