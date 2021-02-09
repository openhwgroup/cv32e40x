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

import uvm_pkg::*;

// Check for FIFO overflows
assert property (@(posedge clk)
                 (fetch_valid_i) |-> (valid_q[DEPTH-1] == 1'b0) )
  else `uvm_error("alignment_buffer", "Fifo Overflow")

// Check that FIFO is cleared the cycle after a branch
assert property (@(posedge clk)
                 (branch_i) |=> (valid_q == 'b0) )
  else `uvm_error("alignment_buffer", "Fifo not cleared after branch")

// Check that FIFO is signaled empty the cycle during a branch
assert property (@(posedge clk)
                   (branch_i) |-> (fifo_cnt_o == 'b0) )
  else `uvm_error("alignment_buffer", "Fifo not empty in branch cycle")

// Check that instr_valid_o is zero when a branch is requested
assert property (@(posedge clk)
                   (branch_i) |-> (instr_valid_o == 1'b0) )
  else `uvm_error("alignment_buffer", "instr_valid_o not zero when branch requested")

