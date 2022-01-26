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
  #(  parameter bit X_EXT     = 1'b0)
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
  input logic           ex_valid_i,
  input logic           wb_ready_i,
  input logic           exception_in_wb,
  input logic [7:0]     exception_cause_wb,
  input logic           rf_we_wb_i,
  input logic           csr_we_i,
  input logic           csr_illegal_i,
  input logic           pending_single_step,
  input logic           trigger_match_in_wb,
  input logic [1:0]     lsu_err_wb_i,
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
  input logic           fencei_ready,
  input logic           xif_commit_kill,
  input logic           xif_commit_valid,
  input logic           nmi_is_store_q,
  input logic           nmi_pending_q,
  input dcsr_t          dcsr_i
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
          (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_wfi_insn && ex_wb_pipe_i.instr_valid) |-> !(id_ex_pipe_i.lsu_en) )
    else `uvm_error("controller", "LSU instruction follows WFI")

  // Check that no instructions are valid in ID or EX when a single step is taken
  // In case of interrupt during step, the instruction being stepped could be in any stage, and will get killed.
  // Exception if first phase of a misaligned LSU gets an MPU error, then 
  // the controller will kill the pipeline and jump to debug with dpc set to exception handler,
  // while id_ex_pipe may still contain the valid last phase of the misaligned LSU
  // todo:ok: Add a second assert to check above exception?
  a_single_step_pipecheck :
    assert property (@(posedge clk) disable iff (!rst_n)
            (pending_single_step && (ctrl_fsm_ns == DEBUG_TAKEN) &&
            (lsu_mpu_status_wb_i == MPU_OK))
            |-> ((!id_ex_pipe_i.instr_valid && !if_id_pipe_i.instr_valid) ||
                (ctrl_fsm_o.irq_ack && ctrl_fsm_o.kill_if && ctrl_fsm_o.kill_id && ctrl_fsm_o.kill_ex && ctrl_fsm_o.kill_wb)))
      else `uvm_error("controller", "ID and EX not empty when when single step is taken")

  // Check trigger match never happens during debug_mode
  a_trigger_match_in_debug :
    assert property (@(posedge clk) disable iff (!rst_n)
            ctrl_fsm_o.debug_mode |-> !trigger_match_in_wb)
      else `uvm_error("controller", "Trigger match during debug mode")

  // Check that lsu_err_wb_i can only be active when an LSU instruction is valid in WB
  // Not using wb_valid, as that is only active for the second half of misaligned.
  // bus error may also be active on the first half, thus checking only for active LSU in WB.
  // Todo: Modify to account for response filter (bufferable writes)
  //a_lsu_err_wb :
  //  assert property (@(posedge clk) disable iff (!rst_n)
  //          lsu_err_wb_i[0] |-> ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.lsu_en)
  //    else `uvm_error("controller", "lsu_error in WB with no valid LSU instruction")

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

  // Assert that intr_taken is always single cycle. I.e. no double counting
  a_mhpevent_intr_taken_single_cycle:
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.mhpmevent.intr_taken |=> !ctrl_fsm_o.mhpmevent.intr_taken)
      else `uvm_error("controller", "mhpmevent.intr_taken not single cycle")

  // Assert that id_ld_stall is always single cycle. I.e. no double counting
  a_mhpevent_id_ld_stall_single_cycle:
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.mhpmevent.id_ld_stall |=> !ctrl_fsm_o.mhpmevent.id_ld_stall)
      else `uvm_error("controller", "mhpmevent.id_ld_stall not single cycle")

  // Assert that id_jalr_stall is a subset of id_invalid
  a_mhpevent_id_jalr_stall_subset:
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.mhpmevent.id_jalr_stall |-> ctrl_fsm_o.mhpmevent.id_invalid)
      else `uvm_error("controller", "mhpmevent.id_jalr_stall not a subset of mhpmevent.id_invalid")
    
  // Assert that id_ld_stall is a subset of id_invalid
  a_mhpevent_id_ld_stall_subset:
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.mhpmevent.id_ld_stall |-> ctrl_fsm_o.mhpmevent.id_invalid)
      else `uvm_error("controller", "mhpmevent.id_ld_stall not a subset of mhpmevent.id_invalid")

  // Assert that wb_data_stall is a subset of wb_invalid
  a_mhpevent_wb_data_stall_subset:
    assert property (@(posedge clk) disable iff (!rst_n)
                     ctrl_fsm_o.mhpmevent.wb_data_stall |-> ctrl_fsm_o.mhpmevent.wb_invalid)
      else `uvm_error("controller", "mhpmevent.wb_data_stall not a subset of mhpmevent.wb_invalid")

  // Assert that interrupts are not allowed when WB stage has an LSU
  // instruction (cnt_q != 0)
  a_block_interrupts:
    assert property (@(posedge clk) disable iff (!rst_n)
                     (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.lsu_en) |-> !interrupt_allowed)
      else `uvm_error("controller", "interrupt_allowed high while LSU is in WB")

// Only include following assertions if X_EXT=1
generate;
  if(X_EXT) begin

    // Assert that a CSR instruction that is accepted by both eXtension interface and pipeline is
    // flagged as killed on the eXtension interface
    a_duplicate_csr_kill:
    assert property (@(posedge clk) disable iff (!rst_n)
                    (id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && !csr_illegal_i &&
                    (id_ex_pipe_i.instr_valid && !ctrl_fsm_o.halt_ex && !ctrl_fsm_o.kill_ex)
                    |-> xif_commit_kill)
      else `uvm_error("controller", "Duplicate CSR instruction not killed")

    // Assert that a CSR instruction that is accepted by both eXtension interface and pipeline
    // causes an illegal instruction
    // TODO: The checks for mpu_status and bus_resp.err below can be removed once the
    //       xif offload is fully implemented (no offload if mpu or bus error occured in IF)
    a_duplicate_csr_illegal:
      assert property (@(posedge clk) disable iff (!rst_n)
                      ex_valid_i && wb_ready_i && (id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && !csr_illegal_i &&
                      !((id_ex_pipe_i.instr.mpu_status != MPU_OK) || (id_ex_pipe_i.instr.bus_resp.err))
                      |=> exception_in_wb && (exception_cause_wb == EXC_CAUSE_ILLEGAL_INSN))
        else `uvm_error("controller", "Duplicate CSR instruction not mardked as illegal")

    // Never kill offloaded instructions in WB (received commit_kill=0 in EX)
    a_offload_kill_wb:
      assert property (@(posedge clk) disable iff (!rst_n)
                        (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.xif_en) |-> !ctrl_fsm_o.kill_wb)
        else `uvm_error("controller", "Offloaded instruction killed in WB")

    // xif_commit_if.commit_valid one cycle per offloaded instruction
    a_single_commit_valid:
      assert property (@(posedge clk) disable iff (!rst_n)
                      (xif_commit_valid && ex_valid_i && !wb_ready_i) |=> !xif_commit_valid until_with (ex_valid_i && wb_ready_i))
        else `uvm_error("controller", "Multiple xif.commit_valid for one instruction")

    // Do not kill commited offloaded instructions if they stay in EX for multiple cycles
    a_nokill_commited_xif:
      assert property (@(posedge clk) disable iff (!rst_n)
                      (xif_commit_valid && ex_valid_i && !wb_ready_i) |=> !ctrl_fsm_o.kill_ex until_with (ex_valid_i && wb_ready_i))
        else `uvm_error("controller", "Committed xif instruction was killed in EX")

    // EX shall be halted if offloaded instruction in WB can cause an exception
    a_halt_ex_xif_exception:
      assert property (@(posedge clk) disable iff (!rst_n)
                      (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.xif_en && ex_wb_pipe_i.xif_meta.exception)
                      |-> ctrl_fsm_o.halt_ex)
        else `uvm_error("controller", "EX not halted while offloaded instruction in WB can cause an exception")

    // Helper logic to check that all offloaded instructions recive commit_valid
    logic commit_valid_flag;
    logic commit_kill_flag;
    always_ff @(posedge clk, negedge rst_n) begin
      if (rst_n == 1'b0) begin
        commit_valid_flag <= 1'b0;
        commit_kill_flag  <= 1'b0;
      end else begin
        // Clear flag if EX is killed or instruction goes to WB
        if(ctrl_fsm_o.kill_ex || (ex_valid_i && wb_ready_i)) begin
          commit_valid_flag <= 1'b0;
          commit_kill_flag  <= 1'b0;
        // Set flag when commit_valid goes high
        end else if(xif_commit_valid) begin
          commit_valid_flag <= 1'b1;
          commit_kill_flag  <= xif_commit_kill;
        end
      end
    end

    // When WB is ready, and EX contains an offloaded instructon,
    // commit_valid must be 1, or must have been one while the instruction
    // was in the EX stage.
    a_offload_commit_valid:
      assert property (@(posedge clk) disable iff (!rst_n)
                      // Xif instruction is in EX, and it either gets killed or goes to WB
                      ((id_ex_pipe_i.instr_valid && id_ex_pipe_i.xif_en && !ctrl_fsm_o.halt_ex) &&
                        (ctrl_fsm_o.kill_ex || wb_ready_i))
                      // Must receive commit_valid, or commit_valid has already been recieved
                      |-> (xif_commit_valid || commit_valid_flag))
        else `uvm_error("controller", "Offloaded instruction did not receive commit_valid")

    // When WB is ready, and EX contains an offloaded instructon that was rejected,
    // commit_kill must be 1, or must have been one while the instruction
    // was in the EX stage.
    a_offload_commit_kill_rejected:
      assert property (@(posedge clk) disable iff (!rst_n)
                      // Rejected Xif instruction is in EX, must be killed
                      ((id_ex_pipe_i.instr_valid && id_ex_pipe_i.xif_en && !id_ex_pipe_i.xif_meta.accepted && !ctrl_fsm_o.halt_ex) &&
                        (ctrl_fsm_o.kill_ex || wb_ready_i))
                      // Must receive commit_kill, or commit_kill has already been recieved
                      |-> (xif_commit_kill || commit_kill_flag))
        else `uvm_error("controller", "Rejected offloaded instruction did not receive commit_kill")

    // Any offloaded instruction that reaches WB must have been accepted by the eXtension interface
    a_offload_in_wb_was_accepted:
      assert property (@(posedge clk) disable iff (!rst_n)
                      (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.xif_en)
                      |-> ex_wb_pipe_i.xif_meta.accepted)
        else `uvm_error("controller", "Offloaded instruction in WB was not preciously accepted by the eXtension interface")

  end
endgenerate

  // Assert that debug is not allowed when WB stage has an LSU
  // instruction (cnt_q != 0)
  a_block_debug:
    assert property (@(posedge clk) disable iff (!rst_n)
                     (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.lsu_en) |-> !debug_allowed)
      else `uvm_error("controller", "debug_allowed high while LSU is in WB")

  // Ensure bubbles in EX and WB while in SLEEP mode
  a_wfi_bubbles:
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_cs == SLEEP) |-> !(ex_wb_pipe_i.instr_valid || id_ex_pipe_i.instr_valid))
      else `uvm_error("controller", "EX and WB stages not empty while in SLEEP state")

  // Assert correct exception cause for mpu load faults (checks default of cause mux)
  a_mpu_re_cause_mux:
    assert property (@(posedge clk) disable iff (!rst_n)
                      (lsu_mpu_status_wb_i == MPU_RE_FAULT) |-> (exception_cause_wb == EXC_CAUSE_LOAD_FAULT))
      else `uvm_error("controller", "Wrong exception cause for MPU read fault")


  // Helper logic to track first occuring bus error
  // Note: Supports max two outstanding transactions
  logic [1:0] outstanding_type;
  logic [1:0] outstanding_count;
  logic bus_error_is_write;
  logic bus_error_latched;
  logic retire_at_error; // 1 if wb_valid_i is high when the bus error is active
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      outstanding_type <= 2'b00;
      outstanding_count <= 2'b00;
      bus_error_latched <= 1'b0;
      bus_error_is_write <= 1'b0;
      retire_at_error <= 1'b0;
    end else begin
      // Req, no rvalid
      if( (m_c_obi_data_if.s_req && m_c_obi_data_if.s_gnt) && !m_c_obi_data_if.s_rvalid) begin
        // Increase outstanding counter
        outstanding_count <= outstanding_count + 2'b01;

        if(outstanding_count == 2'b00) begin
          // No outstanding, assign first entry
          outstanding_type[0] <= m_c_obi_data_if.req_payload.we;
        end else begin
          // One outstanding, shift and assign first entry
          outstanding_type[1] <= outstanding_type[0];
          outstanding_type[0] <= m_c_obi_data_if.req_payload.we;
        end

      // rvalid, no req
      end else if (!(m_c_obi_data_if.s_req && m_c_obi_data_if.s_gnt) && m_c_obi_data_if.s_rvalid) begin
        // Decrease outstanding counter
        outstanding_count <= outstanding_count - 2'b01;

      // req and rvalid
      end else if ((m_c_obi_data_if.s_req && m_c_obi_data_if.s_gnt) && m_c_obi_data_if.s_rvalid) begin
        if (outstanding_count == 2'b10) begin
          // Two outstanding, shift and replace index 0
          outstanding_type[1] <= outstanding_type[0];
          outstanding_type[0] <= m_c_obi_data_if.req_payload.we;
        end else begin
          // One outstanding, replate index 0
          outstanding_type[0] <= m_c_obi_data_if.req_payload.we;
        end
      end


      if(m_c_obi_data_if.s_rvalid && m_c_obi_data_if.resp_payload.err && !bus_error_latched) begin
        bus_error_is_write <= outstanding_count == 2'b01 ? outstanding_type[0] : outstanding_type[1];
        bus_error_latched <= 1'b1;
        retire_at_error <= wb_valid_i;
      end else begin
        if (ctrl_fsm_o.pc_set && ctrl_fsm_o.pc_mux == PC_TRAP_NMI) begin
          bus_error_latched <= 1'b0;
        end
      end
    end
  end

  // Check that controller latches correct type for bus error
  a_latched_bus_error:
    assert property (@(posedge clk) disable iff (!rst_n)
                      (m_c_obi_data_if.s_rvalid && m_c_obi_data_if.resp_payload.err && !bus_error_latched)
                      |=> (nmi_is_store_q == bus_error_is_write) &&
                          (nmi_pending_q == bus_error_latched) && bus_error_latched)
      else `uvm_error("controller", "Wrong type for LSU bus error")



  // Helper logic. Counting number of retired instructions while an NMI is pending outside of debug mode or single stepping.
  logic [1:0] valid_cnt;
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      valid_cnt <= '0;
    end else begin
      if(bus_error_latched) begin
        if(wb_valid_i && !ctrl_fsm_o.debug_mode && !(dcsr_i.step && !dcsr_i.stepie)) begin
          valid_cnt <= valid_cnt + 1;
        end
      end else begin
        valid_cnt <= '0;
      end
    end
  end

  // valid_cnt will start counting one cycle after the LSU bus error has
  // become visible to the core. If an instruction was retired (wb_valid=1)
  // when the bus error arrived, we will allow one more instruction to retire
  // before the NMI is taken (counter < 2). If we didn't retire at the same time as the bus
  // error, we allow two instructions to retire (counter < 3). In any case, max two
  // instructions will retire after the bus error has become visible to the
  // core.
  a_nmi_handler_max_retire:
    assert property (@(posedge clk) disable iff (!rst_n)
                    (valid_cnt < (retire_at_error ? 2'b10 : 2'b11)))
    else `uvm_error("controller", "NMI handler not taken within two instruction retirements")
endmodule // cv32e40x_controller_fsm_sva

