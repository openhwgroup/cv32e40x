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
// Authors:        Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Robert Balas - balasr@iis.ee.ethz.ch                       //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the controller module                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_controller_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  (
   input logic clk,
   input logic rst_n,
   input logic id_ready_i,
   input logic debug_mode_q,
   input logic debug_halted_o,
   input logic debug_running_o,
   input logic debug_havereset_o,
   input logic branch_taken_ex_i,
   input logic debug_single_step_i,
   input logic debug_force_wakeup_n,
   input       ctrl_state_e ctrl_fsm_cs,
   input       ctrl_state_e ctrl_fsm_ns
   );

  // make sure that taken branches do not happen back-to-back, as this is not
  // possible without branch prediction in the IF stage
  a_no_back_to_back_branching :
    assert property (@(posedge clk)
                     (branch_taken_ex_i) |=> (~branch_taken_ex_i) )
      else `uvm_error("controller", "Two branches back-to-back are taken")

  // Ensure DBG_TAKEN_IF can only be enterred if in single step mode or woken
  // up from sleep by debug_req_i
  a_single_step_dbg_taken_if :
    assert property (@(posedge clk)  disable iff (!rst_n)
                     (ctrl_fsm_ns==DBG_TAKEN_IF) |-> ((~debug_mode_q && debug_single_step_i) || debug_force_wakeup_n))
      else `uvm_error("controller", "Assertion a_single_step_dbg_taken_if failed")

        // Ensure DBG_FLUSH state is only one cycle. This implies that cause is either trigger, debug_req_entry, or ebreak
  a_dbg_flush :
    assert property (@(posedge clk)  disable iff (!rst_n)
                     (ctrl_fsm_cs==DBG_FLUSH) |-> (ctrl_fsm_ns!=DBG_FLUSH) )
      else `uvm_error("controller", "Assertion a_dbg_flush failed")

  // Ensure that debug state outputs are one-hot
  a_debug_state_onehot :
    assert property (@(posedge clk)
                     $onehot({debug_havereset_o, debug_running_o, debug_halted_o}))
      else `uvm_error("controller", "Assertion a_debug_state_onehot failed")

  // Ensure that debug_halted_o equals debug_mode_q
  a_debug_halted_equals_debug_mode :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (1'b1) |-> (debug_mode_q == debug_halted_o))
      else `uvm_error("controller", "Assertion a_debug_halted_equals_debug_mode failed")

  // Ensure ID always ready in FIRST_FETCH state
  a_first_fetch_id_ready :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (ctrl_fsm_cs == FIRST_FETCH) |-> (id_ready_i == 1'b1))
      else `uvm_error("controller", "Assertion a_first_fetch_id_ready failed")

  // Ensure that the only way to get to DBG_TAKEN_IF from DBG_FLUSH is if debug_single_step_i is asserted
  a_dbg_flush_to_taken_if :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (ctrl_fsm_cs == DBG_FLUSH) && (ctrl_fsm_ns == DBG_TAKEN_IF) |-> debug_single_step_i)
      else `uvm_error("controller", "Assertion a_dbg_flush_to_taken_if failed")

endmodule // cv32e40x_controller_sva

