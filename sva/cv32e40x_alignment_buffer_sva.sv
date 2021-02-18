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
//                                                                            //
// Authors:        Pasquale Davide Schiavone - pschiavo@iis.ee.ethz.ch        //
//                 Igor Loi - igor.loi@greenwaves-technologies.com            //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the alignment_buffer module             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_alignment_buffer_sva
  import uvm_pkg::*;
  #(parameter DEPTH           = 0,
    parameter FIFO_ADDR_DEPTH = 0)
  (
   input logic                     clk,
   input logic                     rst_n,
   input logic [0:DEPTH-1]         valid_q,
   input logic                     branch_i,
   input logic [31:0]              branch_addr_i,
   input logic [31:0]              fetch_branch_addr_o,
   input logic                     fetch_valid_o,
   input logic [FIFO_ADDR_DEPTH:0] fifo_cnt_n,
   input logic [FIFO_ADDR_DEPTH:0] fifo_cnt_q,
   input logic                     instr_valid_o,
   input logic [31:0]              instr_addr_o,
   input logic                     resp_valid_i,
   input logic                     prefetch_en_i,
   input logic [FIFO_ADDR_DEPTH:0] outstanding_nonflush_cnt,
   input logic                     resp_valid
   );

  logic expect_response;
  assign expect_response = (fifo_cnt_q == 'd0) && (outstanding_nonflush_cnt == 'd1) ||
                           (fifo_cnt_q == 'd0) && (outstanding_nonflush_cnt == 'd2) ||
                           (fifo_cnt_q == 'd1) && (outstanding_nonflush_cnt == 'd1) ||
                           (fifo_cnt_q == 'd2) && (outstanding_nonflush_cnt == 'd1);

  // Capture branch address to check that the next instructions get the correct address
  logic [31:0] next_branch_addr;
  always_ff @(posedge clk, negedge rst_n) begin
    if(rst_n == 1'b0) begin
      next_branch_addr <= 32'd0;
    end else begin      
      if(branch_i) begin
        next_branch_addr <= branch_addr_i;
      end     
    end
  end

  // Check for FIFO overflows
  assert property (@(posedge clk)
                   (resp_valid_i) |-> (valid_q[DEPTH-1] == 1'b0) )
    else `uvm_error("alignment_buffer", "Fifo Overflow")

  // Check that FIFO is cleared the cycle after a branch (R-13.2)
  assert property (@(posedge clk)
                   (branch_i) |=> (valid_q == 'b0) )
    else `uvm_error("alignment_buffer", "Fifo not cleared after branch")

  // Check that FIFO is signaled empty the cycle during a branch
  assert property (@(posedge clk)
                   (branch_i) |-> (fifo_cnt_n == 'b0) )
    else `uvm_error("alignment_buffer", "Fifo not empty in branch cycle")

  // Check that instr_valid_o is zero when a branch is requested (R-13.3)
  assert property (@(posedge clk)
                   (branch_i) |-> (instr_valid_o == 1'b0) )
    else `uvm_error("alignment_buffer", "instr_valid_o not zero when branch requested")

  // Check that no transactions are requested when not supposed to
  // Not including branches
  assert property (@(posedge clk)
    ((fifo_cnt_q > 'd1) ||
    (fifo_cnt_q == 'd1 && outstanding_nonflush_cnt == 'd2)) &&
    !branch_i
    |-> (fetch_valid_o == 1'b0) )
    else `uvm_error("alignment_buffer", "fetch_valid_o active when not supposed to.")

  // Check that we don't get responses where not supposed
  assert property (@(posedge clk)
    (!expect_response) |-> (resp_valid == 1'b0) )
    else `uvm_error("alignment_buffer", "resp_valid_i active when not supposed to.")

  // Check that we request from the prefetcher when a branch occurs
  assert property (@(posedge clk)
    (branch_i) |-> (fetch_valid_o == 1'b1) )
    else `uvm_error("alignment_buffer", "fetch_valid_o not active on a branch.")

  // Check that we change branch_addr to prefetcher correctly (R-13.1)
  assert property (@(posedge clk)
    (branch_i) |-> (fetch_branch_addr_o == {branch_addr_i[31:2], 2'b00}) )
    else `uvm_error("alignment_buffer", "fetch_branch_addr_o not correctly set.")

  // Check that we output correct pc for the first instruction after a branch (R-15.1)
    assert property (@(posedge clk)
    (branch_i) |-> (instr_valid_o) [->1:2] ##0 (instr_addr_o == next_branch_addr))
    else `uvm_error("alignment_buffer", "Wrong pc after branch.")


  // Check that a taken branch can only occur if fetching is requested
    property p_branch_implies_req;
      @(posedge clk) disable iff (!rst_n) (branch_i) |-> (prefetch_en_i);
   endproperty
 
   a_branch_implies_req:
     assert property(p_branch_implies_req)
     else
       `uvm_error("Prefetch Controller SVA",
                  $sformatf("Taken branch occurs while fetching is not requested"))
 

endmodule // cv32e40x_alignment_buffer_sva

