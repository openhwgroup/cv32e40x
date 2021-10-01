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
  input logic           clk,
  input logic           rst_n,
  input logic           debug_mode_q,
  input ctrl_fsm_t      ctrl_fsm_o,
  input logic           jump_taken_id,
  input logic           branch_taken_ex,
  input logic           branch_decision_ex_i,
  input ctrl_state_e    ctrl_fsm_cs,
  input ctrl_state_e    ctrl_fsm_ns,
  input logic [1:0]     lsu_outstanding_cnt,
  input mpu_status_e    lsu_mpu_status_wb_i,
  input logic           if_valid_i,
  input if_id_pipe_t    if_id_pipe_i,
  input id_ex_pipe_t    id_ex_pipe_i,
  input ex_wb_pipe_t    ex_wb_pipe_i,
  input logic           rf_we_wb_i,
  input logic           csr_we_i,
  input logic           pending_single_step,
  input logic           trigger_match_in_wb,
  input logic           lsu_err_wb_i,
  input logic           wb_valid_i,
  input logic           fencei_in_wb,
  input logic           fencei_flush_req_o,
  input logic           fencei_flush_ack_i,
  input logic           fencei_req_and_ack_q,
  input logic           pending_debug,
  input logic           debug_allowed,
  input logic           pending_interrupt,
  input logic           interrupt_allowed,
  input logic           pending_nmi,
  input logic           fencei_ready
);


  // Back-to-back branch should not be possible due to kill of IF/ID stages after branch
  a_no_back_to_back_branch :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (ctrl_fsm_o.pc_set && (ctrl_fsm_o.pc_mux == PC_BRANCH)) |=>
                    !(ctrl_fsm_o.pc_set && (ctrl_fsm_o.pc_mux == PC_BRANCH)))
      else `uvm_error("controller", "Two branches back-to-back are taken")


  // Helper signal
  logic jump_taken;
  assign jump_taken = (ctrl_fsm_o.pc_set && (ctrl_fsm_o.pc_mux == PC_JUMP)) ||
                      (ctrl_fsm_o.pc_set && (ctrl_fsm_o.pc_mux == PC_MRET));

  // Back-to-back jump should not be possible due to kill of IF stage after branch
  a_no_back_to_back_jump :
    assert property (@(posedge clk) disable iff (!rst_n)
                     jump_taken |=> !jump_taken)
      else `uvm_error("controller", "Two jumps back-to-back are taken")

/* todo: fix
  // Check that a jump is taken only when ID is not killed
  a_valid_jump :
    assert property (@(posedge clk)
                     jump_taken |-> if_id_pipe_i.instr_valid && !ctrl_fsm_o.kill_id)
      else `uvm_error("controller", "Jump taken while ID is halted or killed")
*/

// Check that xret does not coincide with CSR write (to avoid using wrong return address)
  // This check is more strict than really needed; a CSR instruction would be allowed in EX as long
  // as its write action happens before the xret CSR usage
  property p_xret_csr;
    @(posedge clk) disable iff (!rst_n)
      (ctrl_fsm_o.pc_set && ((ctrl_fsm_o.pc_mux == PC_MRET) || (ctrl_fsm_o.pc_mux == PC_DRET))) |->
                                (!(ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.csr_en && csr_we_i));
  endproperty

  a_xret_csr : assert property(p_xret_csr) else `uvm_error("controller", "Assertion a_xret_csr failed")

  // make sure that branch decision is valid when jumping
  a_br_decision :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (id_ex_pipe_i.branch_in_ex) |-> (branch_decision_ex_i !== 1'bx) )
      else begin `uvm_error("controller", $sformatf("%t, Branch decision is X in module %m", $time)); end

  // Ensure that debug state outputs are one-hot
  a_debug_state_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot({ctrl_fsm_o.debug_havereset, ctrl_fsm_o.debug_running, ctrl_fsm_o.debug_halted}))
      else `uvm_error("controller", "Assertion a_debug_state_onehot failed")

  // Ensure that debug_halted_o equals debug_mode_q
  a_debug_halted_equals_debug_mode :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (1'b1) |-> (debug_mode_q == ctrl_fsm_o.debug_halted))
      else `uvm_error("controller", "Assertion a_debug_halted_equals_debug_mode failed")

  // Ensure no interrupt is taken if LSU has outstanding transactions
  a_no_irq_on_outstanding_obi :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_o.irq_ack) |-> (lsu_outstanding_cnt == 2'b00) )
      else `uvm_error("controller", "Interrupt taken while oustanding transactions are pending")

  // Ensure <stage>.instr_valid is zero following a kill_<prev_stage>
 /* TODO:OK:low Failing when bubble is inserted in ID (id_ready_o==0) when WFI is in EX. 
            Will investigate how to solve. Agreed that this assertion is maybe too strict. We only need to guarantee that if a stage is killed, that the instruction in that stage never reaches the following stage with instr_valid = 1 (it doesn't need instr_valid of the next stage 0 in the following cycle.
  a_kill_if :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_o.kill_if) |=> (if_id_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "if_id_pipe.instr_valid not zero after kill_if")
*/
/* TODO:OK:low Failing when a DIV instruction is being executed
           Causes ex_ready to be 0. Will be fixed then divider is interruptable
  a_kill_id :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_o.kill_id) |=> (id_ex_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "id_ex_pipe.instr_valid not zero after kill_id")
*/
  a_kill_ex :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_o.kill_ex && !ctrl_fsm_o.halt_wb) |=> (ex_wb_pipe_i.instr_valid == 1'b0) )
    else `uvm_error("controller", "ex_wb_pipe.instr_valid not zero after kill_ex")

  a_kill_wb_rf :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_o.kill_wb) |-> (rf_we_wb_i == 1'b0) )
    else `uvm_error("controller", "regfile written when kill_wb is asserted")

  a_kill_wb_csr :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_o.kill_wb) |-> (!csr_we_i) )
    else `uvm_error("controller", "csr written while kill_wb is asserted")

  // Check that no stages have valid instructions using RESET or BOOT_SET
  a_reset_if_csr :
    assert property (@(posedge clk) disable iff (!rst_n)
            ((ctrl_fsm_cs == RESET) || (ctrl_fsm_cs == BOOT_SET)) |-> (!if_valid_i && !if_id_pipe_i.instr_valid && !id_ex_pipe_i.instr_valid && !ex_wb_pipe_i.instr_valid) )
      else `uvm_error("controller", "Instruction valid during RESET or BOOT_SET")

  // Check that no LSU insn can be in EX when there is a WFI in WB
  a_wfi_lsu_csr :
  assert property (@(posedge clk) disable iff (!rst_n)
          (ex_wb_pipe_i.wfi_insn && ex_wb_pipe_i.instr_valid) |-> !(id_ex_pipe_i.lsu_en) )
    else `uvm_error("controller", "LSU instruction follows WFI")

  // Check that no instructions are valid in ID or EX when a single step is taken
  // Exception if first phase of a misaligned LSU gets an MPU error, then 
  // the controller will kill the pipeline and jump to debug with dpc set to exception handler,
  // while id_ex_pipe may still contain the valid last phase of the misaligned LSU
  // todo:ok: Add a second assert to check above exception?
  a_single_step_pipecheck :
    assert property (@(posedge clk) disable iff (!rst_n)
            (pending_single_step && (ctrl_fsm_ns == DEBUG_TAKEN) &&
            (lsu_mpu_status_wb_i == MPU_OK))
            |-> (!id_ex_pipe_i.instr_valid && !if_id_pipe_i.instr_valid))
      else `uvm_error("controller", "ID and EX not empty when when single step is taken")

  // Check trigger match never happens during debug_mode
  a_trigger_match_in_debug :
    assert property (@(posedge clk) disable iff (!rst_n)
            ctrl_fsm_o.debug_mode |-> !trigger_match_in_wb)
      else `uvm_error("controller", "Trigger match during debug mode")

  // Check that lsu_err_wb_i can only be active when an LSU instruction is valid in WB
  // Not using wb_valid, as that is only active for the second half of misaligned.
  // bus error may also be active on the first half, thus checking only for active LSU in WB.
  a_lsu_err_wb :
    assert property (@(posedge clk) disable iff (!rst_n)
            lsu_err_wb_i |-> ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.lsu_en)
      else `uvm_error("controller", "lsu_error in WB with no valid LSU instruction")

  // Check that fencei handshake is only exersiced when there's a fencei in the writeback stage
  a_fencei_hndshk_fencei_wb :
    assert property (@(posedge clk) disable iff (!rst_n)
           fencei_flush_req_o |-> fencei_in_wb)
      else `uvm_error("controller", "Fencei request when no fencei in writeback")    

  // Assert that the fencei request is set the cycle after fencei instruction enters WB (if fencei_ready=1 and there are no higher priority events)
  a_fencei_hndshk_req_when_fencei_wb :
    assert property (@(posedge clk) disable iff (!rst_n)
           $rose(fencei_in_wb && fencei_ready) && !(pending_nmi || (pending_debug && debug_allowed) || (pending_interrupt && interrupt_allowed)) 
                     |=> $rose(fencei_flush_req_o))
      else `uvm_error("controller", "Fencei in WB did not result in fencei_flush_req_o")

  // Only clear fencei request when acknowledged
  //  ##1 is added to prevent $fell from triggering in cycle 1
  a_fencei_hndshk_ack_b4_req_clear :
    assert property (@(posedge clk) disable iff (!rst_n)
           ##1 $fell(fencei_flush_req_o) |-> $past(fencei_flush_ack_i))
      else `uvm_error("controller", "Fencei request cleared before ack")

  // Clearing of fencei_flush_req_o is always followed by wb_valid (meaning that the fence.i fully completed)
  //  ##1 is added to prevent $fell from triggering in cycle 1
  a_fencei_wb_valid :
    assert property (@(posedge clk) disable iff (!rst_n)
           ##1 $fell(fencei_flush_req_o) |-> wb_valid_i)
      else `uvm_error("controller", "Fencei handshake completion not followed by wb_valid")
    
  // assert that fencei_flush_req_o goes low the cycle after req&&ack
  a_fencei_clear_req :
    assert property (@(posedge clk) disable iff (!rst_n)
                     fencei_flush_req_o && fencei_flush_ack_i |=> !fencei_flush_req_o)
      else `uvm_error("controller", "fencei_flush_req_o not cleared after req&&ack")

  // assert no lingering fencei handshake when a fencei instruction enters WB.
  a_fencei_lingering_req :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $rose(fencei_in_wb) |-> !(fencei_flush_req_o || fencei_req_and_ack_q))
      else `uvm_error("controller", "Fencei handshake not idle when fencei instruction entered writeback")

  // assert that the fencei_ready signal (i.e. write buffer empty) is always set when fencei handshake is active
  a_fencei_ready :
    assert property (@(posedge clk) disable iff (!rst_n)
                     fencei_flush_req_o |-> fencei_ready)
      else `uvm_error("controller", "Fencei handshake active while fencei_ready = 0")
    
  // assert that NMI's are not reported on irq_ack
  a_irq_ack_no_nmi :
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.irq_ack |-> !pending_nmi)
      else `uvm_error("controller", "irq_ack set while there's a pending NMI")

endmodule // cv32e40x_controller_fsm_sva

