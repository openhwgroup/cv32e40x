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
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    RTL assertions for the controller module                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_controller_fsm_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  (
   input logic clk,
   input logic rst_n,
   input logic debug_mode_q,
   input logic debug_halted_o,
   input logic debug_running_o,
   input logic debug_havereset_o,
   input logic branch_taken_ex_i,
   input       ctrl_state_e ctrl_fsm_cs,
   input       ctrl_state_e ctrl_fsm_ns,
   input logic irq_ack_o,
   input logic [1:0] lsu_outstanding_cnt
   );

  // make sure that taken branches do not happen back-to-back, as this is not
  // possible without branch prediction in the IF stage
  a_no_back_to_back_branching :
    assert property (@(posedge clk)
                     (branch_taken_ex_i) |=> (~branch_taken_ex_i) )
      else `uvm_error("controller", "Two branches back-to-back are taken")

  
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

  // Ensure no interrupt is taken if LSU has outstanding transactions
  a_no_irq_on_outstanding_obi :
    assert property (@(posedge clk)
                      (irq_ack_o) |-> (lsu_outstanding_cnt == 2'b00) )
      else `uvm_error("controller", "Interrupt taken while oustanding transactions are pending")

endmodule // cv32e40x_controller_fsm_sva

