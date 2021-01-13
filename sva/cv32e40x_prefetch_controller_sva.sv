// Copyright 2020 Silicon Labs, Inc.
//   
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//   
//     https://solderpad.org/licenses/SHL-2.0/
//   
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License 
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Design Name:    Prefetcher Controller SVA                                  //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    SV Properties, Assertions, etc, for the CV32E40P           //
//                 Prefetch Controller.                                       //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_prefetch_controller_sva
#(
  parameter DEPTH = 4,
  parameter PULP_OBI = 0 ,
  parameter FIFO_ADDR_DEPTH = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
  input  logic        clk,
  input  logic        rst_n,

  // Fetch stage interface
  input  logic        req_i,                    // Fetch stage requests instructions
  input  logic        branch_i,                 // Taken branch
  input  logic [31:0] branch_addr_i,            // Taken branch address (only valid when branch_i = 1)
  input  logic        busy_o,                   // Prefetcher busy

  // Transaction request interface
  input  logic        trans_valid_o,            // Transaction request valid (to bus interface adapter)
  input  logic        trans_ready_i,            // Transaction request ready (transaction gets accepted when trans_valid_o and trans_ready_i are both 1)
  input  logic [31:0] trans_addr_o,             // Transaction address (only valid when trans_valid_o = 1). No stability requirements.

  // Fetch interface is ready/valid
  input  logic                     fetch_ready_i,
  input  logic                     fetch_valid_o,

  // Transaction response interface
  input  logic        resp_valid_i,             // Note: Consumer is assumed to be 'ready' whenever resp_valid_i = 1

  // FIFO interface
  input  logic [FIFO_ADDR_DEPTH:0] fifo_cnt_i,               // Number of valid items/words in the prefetch FIFO
  input  logic        fifo_empty_i,             // FIFO is empty

  // internals used by these assertions
  input  logic [FIFO_ADDR_DEPTH:0] cnt_q,
  input  logic        count_up,
  input  logic        count_down
);

  import uvm_pkg::*; // needed for the UVM messaging service (`uvm_error(), etc.)

  // Check that outstanding transaction count will not overflow DEPTH
  property p_no_transaction_count_overflow_0;
     @(posedge clk) disable iff (!rst_n) (1'b1) |-> (cnt_q <= DEPTH);
  endproperty

  a_no_transaction_count_overflow_0:
    assert property(p_no_transaction_count_overflow_0)
    else
      `uvm_error("Prefetch Controller SVA",
                 $sformatf("Outstanding transaction count (%0d) greater than DEPTH (%0d)",
                           cnt_q, DEPTH))

  property p_no_transaction_count_overflow_1;
     @(posedge clk) disable iff (!rst_n) (cnt_q == DEPTH) |-> (!count_up || count_down);
  endproperty

  a_no_transaction_count_overflow_1:
    assert property(p_no_transaction_count_overflow_1)
    else
      `uvm_error("Prefetch Controller SVA",
                 $sformatf("Overflow condition detected: cnt_q==%0d, DEPTH==%0d, count_up==%0d, count_down==%0d",
                           cnt_q, DEPTH, count_up, count_down))


 // Check that a taken branch can only occur if fetching is requested
  property p_branch_implies_req;
     @(posedge clk) disable iff (!rst_n) (branch_i) |-> (req_i);
  endproperty

  a_branch_implies_req:
    assert property(p_branch_implies_req)
    else
      `uvm_error("Prefetch Controller SVA",
                 $sformatf("Taken branch occurs while fetching is not requested"))

  // Check that after a taken branch the initial FIFO output is not accepted
  property p_branch_invalidates_fifo;
     @(posedge clk) disable iff (!rst_n) (branch_i) |-> (!(fetch_valid_o && fetch_ready_i));
  endproperty

  a_branch_invalidates_fifo:
    assert property(p_branch_invalidates_fifo)
    else
      `uvm_error("Prefetch Controller SVA",
                 $sformatf("After taken branch the initial FIFO output is accepted"))

endmodule: cv32e40x_prefetch_controller_sva
