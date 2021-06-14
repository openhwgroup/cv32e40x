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
   input logic branch_taken_ex,
   input       ctrl_state_e ctrl_fsm_cs,
   input       ctrl_state_e ctrl_fsm_ns,
   input logic irq_ack_o,
   input logic [1:0] lsu_outstanding_cnt,
   input logic kill_if_o,
   input logic kill_id_o,
   input logic kill_ex_o,
   input logic kill_wb_o,
   input logic if_valid_i,
   input if_id_pipe_t if_id_pipe_i,
   input id_ex_pipe_t id_ex_pipe_i,
   input ex_wb_pipe_t ex_wb_pipe_i,
   input logic rf_we_wb_i,
   input csr_opcode_e csr_op_i
   );

  // TODO: This assertion has been removed for a simplification for RVFI and has not been verified
  // make sure that taken branches do not happen back-to-back, as this is not
  // possible without branch prediction in the IF stage
  //a_no_back_to_back_branching :
  //  assert property (@(posedge clk)
  //                   (branch_taken_ex) |=> (~branch_taken_ex) )
  //    else `uvm_error("controller", "Two branches back-to-back are taken")

  
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

  // Ensure <stage>.instr_valid is zero following a kill_<prev_stage>
 /* TODO:OK Failing when bubble is inserted in ID (id_ready_o==0) when WFI is in EX. 
            Will investigate how to solve
  a_kill_if :
  assert property (@(posedge clk)
                    (kill_if_o) |=> (if_id_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "if_id_pipe.instr_valid not zero after kill_if")
*/
/* TODO:OK Failing when a DIV instruction is being executed
           Causes ex_ready to be 0. Will be fixed then divider is interruptable
  a_kill_id :
  assert property (@(posedge clk)
                    (kill_id_o) |=> (id_ex_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "id_ex_pipe.instr_valid not zero after kill_id")
*/
  a_kill_ex :
  assert property (@(posedge clk)
                    (kill_ex_o) |=> (ex_wb_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "ex_wb_pipe.instr_valid not zero after kill_ex")

  a_kill_wb_rf :
  assert property (@(posedge clk)
                    (kill_wb_o) |-> (rf_we_wb_i == 1'b0) )
    else `uvm_error("controller", "regfile written when kill_wb is asserted")

  a_kill_wb_csr :
  assert property (@(posedge clk)
                    (kill_wb_o) |-> (csr_op_i == CSR_OP_READ) )
    else `uvm_error("controller", "csr written while kill_wb is asserted")

  // Check that no stages have valid instructions using RESET or BOOT_SET
  a_reset_if_csr :
    assert property (@(posedge clk)
            ((ctrl_fsm_cs == RESET) || (ctrl_fsm_cs == BOOT_SET)) |-> (!if_valid_i && !if_id_pipe_i.instr_valid && !id_ex_pipe_i.instr_valid && !ex_wb_pipe_i.instr_valid) )
      else `uvm_error("controller", "Instruction valid during RESET or BOOT_SET")

  // Check that no LSU insn can be in EX when there is a WFI in WB
  a_wfi_lsu_csr :
  assert property (@(posedge clk)
          (ex_wb_pipe_i.wfi_insn && ex_wb_pipe_i.instr_valid) |-> !(id_ex_pipe_i.data_req) )
    else `uvm_error("controller", "LSU instruction follows WFI")
endmodule // cv32e40x_controller_fsm_sva

