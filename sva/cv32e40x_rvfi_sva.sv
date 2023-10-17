// Copyright 2021 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    Assertions for RVFI                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_rvfi_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  import cv32e40x_rvfi_pkg::*;
#(
    parameter bit     CLIC  = 0,
    parameter bit     DEBUG = 1,
    parameter a_ext_e A_EXT = A_NONE
)
(
   input logic             clk_i,
   input logic             rst_ni,

   input logic             rvfi_valid,
   input rvfi_intr_t       rvfi_intr,
   input rvfi_trap_t       rvfi_trap,
   input logic [2:0]       rvfi_dbg,

   input ctrl_fsm_t        ctrl_fsm_i,
   input logic [31:0]      rvfi_csr_dcsr_rdata,
   input logic [31:0]      rvfi_csr_mcause_rdata,
   input logic [31:0]      rvfi_pc_rdata,
   input logic [24:0]      mtvec_addr_i,
   input logic [31:0]      rvfi_csr_mie_rdata,
   input logic [31:0]      rvfi_csr_mip_rdata,
   input logic             irq_ack,
   input logic             dbg_ack,
   input logic             ebreak_in_wb_i,
   input rvfi_intr_t [4:0] in_trap,
   input logic [4:0] [2:0] debug_cause,

   input logic             if_valid_i,
   input logic             id_ready_i,
   input logic [31:0]      pc_if_i,
   input logic [31:0]      pc_id_i,
   input logic [31:0]      pc_ex_i,
   input logic [31:0]      pc_wb_i,
   input inst_resp_t       prefetch_instr_if_i,
   input logic             prefetch_compressed_if_i,
   input  logic [31:0]     prefetch_addr_if_i,
   input  logic            prefetch_valid_if_i,
   input  logic            prefetch_ready_if_i,
   input rvfi_obi_instr_t  obi_instr_if,
   input rvfi_obi_instr_t [0:3] obi_instr_fifo_q,
   input logic [1:0]       obi_instr_rptr_q_inc,
   input logic [1:0]       obi_instr_rptr_q,
   input logic             mret_ptr_wb,
   input logic [31:0]      instr_rdata_wb_past,
   input lsu_atomic_e      lsu_atomic_wb_i,
   input logic             lsu_en_wb_i,
   input logic             lsu_split_q_wb_i,
   input logic             pc_mux_exception,
   input logic             pc_mux_debug,
   input logic             in_trap_clr,
   input logic             wb_valid_lastop,
   input logic             etrigger_in_wb_i,

   cv32e40x_if_c_obi.monitor  m_c_obi_data_if,
   input logic [32*NMEM-1:0]  rvfi_mem_addr,
   input logic [ 4*NMEM-1:0]  rvfi_mem_rmask,
   input logic [ 4*NMEM-1:0]  rvfi_mem_wmask,
   input logic [32*NMEM-1:0]  rvfi_mem_rdata,
   input logic [32*NMEM-1:0]  rvfi_mem_wdata,
   input logic [ 1*NMEM-1:0]  rvfi_mem_exokay,
   input logic [ 1*NMEM-1:0]  rvfi_mem_err,
   input logic [ 3*NMEM-1:0]  rvfi_mem_prot,
   input logic [ 6*NMEM-1:0]  rvfi_mem_atop,
   input logic [ 2*NMEM-1:0]  rvfi_mem_memtype,
   input logic [ 1*NMEM-1:0]  rvfi_mem_dbg
);

  if (CLIC) begin
    a_mret_pointer :
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                    (mret_ptr_wb |-> (instr_rdata_wb_past == 32'h30200073)))
      else `uvm_error("rvfi", "mret not in STAGE_WB_PAST when mret pointer arrived in WB")
  end

  // Check that irq_ack results in RVFI capturing a trap
  // Ideally, we should assert that every irq_ack eventually leads to rvfi_intr,
  // but since there can be an infinite delay between irq_ack and rvfi_intr (e.g. because of bus stalls), we're settling for asserting
  // that irq_ack leads to RVFI capturing a trap (in_trap[IF_STAGE] = 1)

  a_irq_ack_rvfi_capture :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                    (irq_ack |=> in_trap[STAGE_IF].intr))
      else `uvm_error("rvfi", "irq_ack not captured by RVFI")

  // Every irq_ack shall cause rvfi_intr on next rvfi_valid
  property p_every_ack_followed_by_rvfi_intr;
    @(posedge clk_i) disable iff (!rst_ni)
    irq_ack ##1 rvfi_valid[->1]
      |->
        rvfi_intr.intr;
  endproperty : p_every_ack_followed_by_rvfi_intr

  a_every_ack_followed_by_rvfi_intr: assert property (p_every_ack_followed_by_rvfi_intr)
  else
    `uvm_error("rvfi",
      $sformatf("Every irq_ack should be followed by the corresponding rvfi_intr"));

  // rvfi_intr.intr shall also have rvfi_intr.exception or rvfi_intr.interrupt set at the same time
  property p_rvfi_intr_interrupt_exception;
    @(posedge clk_i) disable iff (!rst_ni)
    rvfi_intr.intr
      |->
        (rvfi_intr.interrupt ||
        rvfi_intr.exception);
  endproperty : p_rvfi_intr_interrupt_exception

  a_rvfi_intr_interrupt_exception: assert property (p_rvfi_intr_interrupt_exception)
  else
    `uvm_error("rvfi",
      $sformatf("rvfi_intr.intr set without rvfi_intr.exception or rvfi_intr.interrupt"));


  // Sequence used to locate rvfi_valid following rvfi_valid with prereq set
  sequence s_goto_next_rvfi_valid(prereq);
    (prereq && rvfi_valid) ##1 rvfi_valid[->1];
  endsequence

  logic no_debug;

  // Indicate debug mode, or single stepping
  assign no_debug = !(rvfi_csr_dcsr_rdata[2] || ctrl_fsm_i.debug_mode);

  // rvfi_trap should always be followed by rvfi_intr (as long as we're not in debug mode)
  a_rvfi_trap_intr :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     no_debug throughout s_goto_next_rvfi_valid(|rvfi_trap) |->
                     rvfi_intr.intr)
      else `uvm_error("rvfi", "rvfi_trap not followed by rvfi_intr")

  // Exception code in rvfi_trap.exception_cause should align with mcause exception cause in the following retired instruction
  // This is exempt if we have an NMI, because NMI will result in mcause being updated in between retired instructions.
  // Also, in debug mode, mcause is not updated.
  a_rvfi_trap_mcause_align:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                    (no_debug && !ctrl_fsm_i.pending_nmi) throughout s_goto_next_rvfi_valid(|rvfi_trap) |->
                     rvfi_intr.intr && (rvfi_csr_mcause_rdata[5:0] == $past(rvfi_trap.exception_cause)))
      else `uvm_error("rvfi", "rvfi_trap.exception_cause not consistent with mcause[5:0] in following retired instruction")


  // Check that the trap is always signalled on the instruction before single step debug entry (unless killed by interrupt)
  a_rvfi_single_step_no_trap_no_dbg_entry:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     s_goto_next_rvfi_valid(rvfi_trap.debug_cause != DBG_CAUSE_STEP) |-> ((rvfi_dbg != DBG_CAUSE_STEP) || rvfi_intr.intr))
     else `uvm_error("rvfi", "Single step debug entry without correct rvfi_trap first")



if (DEBUG) begin
  // Helper signal, indicating debug cause
  // Special case for debug entry from debug mode caused by EBREAK as it is not captured by debug_cause_i
  logic [2:0] debug_cause_int;
  assign debug_cause_int = (ctrl_fsm_i.debug_mode && ebreak_in_wb_i) ? 3'h1 : ctrl_fsm_i.debug_cause;

  // Check that dbg_ack results in RVFI capturing a debug_cause
  // Ideally, we should assert that every dbg_ack eventually leads to rvfi_dbg,
  // but since there can be an infinite delay between dbg_ack and rvfi_dbg (e.g. because of bus stalls), we're settling for asserting
  // that dbg_ack leads to RVFI capturing the debug cause
  a_dbg_ack_rvfi_capture :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (dbg_ack |=> (debug_cause[STAGE_IF] == $past(debug_cause_int))))
            else `uvm_error("rvfi", "dbg_ack did not lead to rvfi_dbg != 0")

  // Helper signal, indicate that a debug entry was signaled on RVFI
  logic  rvfi_dbg_ack;
  assign rvfi_dbg_ack = |rvfi_dbg && rvfi_valid;

  // Helper signal, count outstanding dbg_ack
  bit [1:0] dbg_ack_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dbg_ack_cnt <= '0;
    end
    else begin
      if (dbg_ack && !rvfi_dbg_ack) begin
        dbg_ack_cnt <= dbg_ack_cnt+2'd1;
      end
      else if (rvfi_dbg_ack && !dbg_ack) begin
        dbg_ack_cnt <= dbg_ack_cnt-2'd1;
      end
    end
  end
  // Check that rvfi_dbg_ack is preceeded by dbg_ack
  a_rvfi_dbg_dbg_ack :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (rvfi_dbg_ack |-> (dbg_ack_cnt != 0)))
      else `uvm_error("rvfi", "rvfi_dbg not preceeded by dbg_ack")

  // rvfi_trap[2] should always be followed by rvfi_dbg
  a_rvfi_trap_dbg :
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                    s_goto_next_rvfi_valid(rvfi_trap.debug) |->
                    rvfi_dbg != '0)
    else `uvm_error("rvfi", "rvfi_trap.debug not followed by rvfi_dbg")

  // Exception code in rvfi_trap[11:9] should align with rvfi_dbg the following retired instruction
  a_rvfi_trap_rvfi_dbg_align:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                    s_goto_next_rvfi_valid(rvfi_trap.debug) |->
                    rvfi_dbg == $past(rvfi_trap.debug_cause))
    else `uvm_error("rvfi", "rvfi_trap.debug_cause not consistent with rvfi_dbg in following retired instruction")

  // Check that rvfi_trap always indicate single step or etrigger if rvfi_trap[2:1] == 2'b11
  a_rvfi_single_step_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                    rvfi_valid && rvfi_trap.exception && rvfi_trap.debug
                    |->
                    (rvfi_trap.debug_cause == DBG_CAUSE_STEP)
                    or
                    (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER) && $past(etrigger_in_wb_i))
    else `uvm_error("rvfi", "rvfi_trap[2:1] == 2'b11, but debug cause bits do not indicate single stepping or trigger")

  // Check that dcsr.cause and mcause exception align with rvfi_trap when rvfi_trap[2:1] == 2'b11
  // rvfi_intr should also always be set in this case
  a_rvfi_trap_step_exception:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                    s_goto_next_rvfi_valid(rvfi_trap.exception && rvfi_trap.debug)
                    |->
                    ((rvfi_dbg == DBG_CAUSE_STEP) && (rvfi_csr_dcsr_rdata[8:6] == DBG_CAUSE_STEP) ||
                     (rvfi_dbg == DBG_CAUSE_TRIGGER) && (rvfi_csr_dcsr_rdata[8:6] == DBG_CAUSE_TRIGGER)) &&
                    (rvfi_csr_mcause_rdata[5:0] == $past(rvfi_trap.exception_cause)) &&
                    rvfi_intr.intr)
    else `uvm_error("rvfi", "dcsr.cause, mcause and rvfi_intr not as expected following an exception during single step")

  // When dcsr.nmip is set, the next retired instruction should be the NMI handler (except in debug mode).
  // rvfi_intr should also be set. Checking when ctrl_fsm_i.nmi_mtvec_is stable as the mtvec index may change in CLINT mode.
  a_rvfi_nmip_nmi_handler:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                    (no_debug && $stable(mtvec_addr_i) && $stable(ctrl_fsm_i.nmi_mtvec_index)) throughout s_goto_next_rvfi_valid(rvfi_csr_dcsr_rdata[3]) |->
                    rvfi_intr.intr &&
                    (rvfi_pc_rdata == {mtvec_addr_i, ctrl_fsm_i.nmi_mtvec_index, 2'b00}) &&
                    ((rvfi_csr_mcause_rdata[10:0] == INT_CAUSE_LSU_LOAD_FAULT) || (rvfi_csr_mcause_rdata[10:0] == INT_CAUSE_LSU_STORE_FAULT)))
    else `uvm_error("rvfi", "dcsr.nmip not followed by rvfi_intr and NMI handler")
end

if ((A_EXT == A) || (A_EXT == ZALRSC)) begin
  // Aligned atomics blocked by the PMA shall use the EXC_CAUSE_LOAD_FAULT or EXC_CAUSE_STORE_FAULT exception codes with
  // cause_type MEM_ERR_ATOMIC.
  //
  // Misaligned atomics to a non-main PMA region shall use EXC_CAUSE_LOAD_FAULT or EXC_CAUSE_STORE_FAULT exception codes with
  // cause_type MEM_ERR_IO_ALIGN
  //
  // Misaligned atomics which are otherwise not blocked by the PMA (cfg is main and atomic) shall use either
  // EXC_CAUSE_LOAD_MISALIGNED or EXC_CAUSE_STORE_MISALIGNED with cause_type MEM_ERR_IO_ALIGN.
  a_aligned_lr_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_LR) && lsu_en_wb_i &&
                  !lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  (rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_FAULT))
    else `uvm_error("rvfi", "Exception on aligned LR.W atomic instruction did not set correct cause_type in rvfi_trap")

  a_misaligned_lr_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_LR) && lsu_en_wb_i &&
                  lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_MISALIGNED))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_FAULT))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_FAULT)))
    else `uvm_error("rvfi", "Exception on misaligned LR.W atomic instruction did not set correct cause_type in rvfi_trap")

  a_aligned_sc_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_SC) && lsu_en_wb_i &&
                  !lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  (rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT))
    else `uvm_error("rvfi", "Exception on aligned SC.W atomic instruction did not set correct cause_type in rvfi_trap")

  a_misaligned_sc_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_SC) && lsu_en_wb_i &&
                  lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_MISALIGNED))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT)))
    else `uvm_error("rvfi", "Exception on misaligned SC.W atomic instruction did not set correct cause_type in rvfi_trap")
end

if (A_EXT == A) begin
  a_aligned_amo_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_AMO) && lsu_en_wb_i &&
                  !lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  (rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT))
    else `uvm_error("rvfi", "Exception on aligned AMO* atomic instruction did not set correct cause_type in rvfi_trap")

  a_misaligned_amo_access_fault_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_exception && (lsu_atomic_wb_i == AT_AMO) && lsu_en_wb_i &&
                  lsu_split_q_wb_i
                  |=>
                  rvfi_valid &&
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_MISALIGNED))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_ATOMIC) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT))
                  or
                  ((rvfi_trap.cause_type == MEM_ERR_IO_ALIGN) &&
                  (rvfi_trap.exception_cause == EXC_CAUSE_STORE_FAULT)))
    else `uvm_error("rvfi", "Exception on misaligned AMO* atomic instruction did not set correct cause_type in rvfi_trap")
end

  // An external haltrequest will kill all pipeline stages. Check that in_trap_clr is never true for such debug entries.
  // in_trap_clr == 1 means that the rvfi_intr associated with the first instruction of an interrupt- or exception handler
  // has reached RVFI outputs, and any internal tracking of this state within RVFI can be cleared. Killing all stages makes this
  // tracked in_trap to not reach RVFI outputs.
  a_no_clr_on_haltreq:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  (pc_mux_debug) &&
                  (ctrl_fsm_i.debug_cause == DBG_CAUSE_HALTREQ)
                  |->
                  !in_trap_clr)
    else `uvm_error("rvfi", "in_trap_clr is active when going to debug due to external haltrequest")

  // If the WB stage of RVFI contains an in_trap at the time of synchronous debug entry, the in_trap_clr
  // must be 1, signaling that the trap info reached rvfi_intr and any internal tracking must be cleared.
  a_clr_on_sync_dbg_entry:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  (pc_mux_debug) &&
                  in_trap[STAGE_WB].intr &&
                  (ctrl_fsm_i.debug_cause != DBG_CAUSE_HALTREQ)
                  |->
                  in_trap_clr)
    else `uvm_error("rvfi", "in_trap_clr not active when going to debug due to a synchronous cause")

  // Check that no other in_trap than the one in WB can be present in the pipeline at the same time.
  a_single_in_trap_tracked:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  in_trap_clr
                  |->
                  !((in_trap[STAGE_EX] && (pc_wb_i != pc_ex_i)) ||
                    (in_trap[STAGE_ID] && (pc_wb_i != pc_id_i)) ||
                    (in_trap[STAGE_IF] && (pc_wb_i != pc_if_i))))
    else `uvm_error("rvfi", "More than one in_trap at the same time")

  // Check that rvfi_valid and rvfi_trap.debug is correctly set for single step.
  //
  a_single_step_rvfi_valid_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_debug &&                                // Debug entry (DEBUG_TAKEN)
                  (ctrl_fsm_i.debug_cause == DBG_CAUSE_STEP) &&  // due to single step
                  $past(wb_valid_lastop)                         // An instruction was retired previous cycle
                  |->
                  (rvfi_valid && rvfi_trap.debug))               // Must set rvfi_valid and trap.debug
    else `uvm_error("rvfi", "No rvfi_valid or rvfi_trap for single step.")

  // Check that rvfi_valid and rvfi_trap.debug is correctly set for etrigger.
  //
  a_etrigger_rvfi_valid_trap:
  assert property (@(posedge clk_i) disable iff (!rst_ni)
                  pc_mux_debug &&                                         // Debug entry (DEBUG_TAKEN)
                  (ctrl_fsm_i.debug_cause == DBG_CAUSE_TRIGGER) &&        // due to trigger
                  $past(wb_valid_lastop)                                  // Triggers other than etrigger halts pipeline, this must be etrigger
                  |->
                  (rvfi_valid && rvfi_trap.debug && rvfi_trap.exception)) // Must set rvfi_valid and trap.debug + trap.exception

    else `uvm_error("rvfi", "No rvfi_valid or rvfi_trap for etrigger.")


  // Check that cv32e40x_rvfi_instr_obi tracks alignment buffer
  a_rvfi_instr_obi_addr:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     if_valid_i && id_ready_i && (obi_instr_if.resp_payload.mpu_status == MPU_OK) |->
                     (pc_if_i[31:2] == obi_instr_if.req_payload.addr[31:2]))
      else `uvm_error("rvfi", "rvfi_instr_obi addr does not track alignment buffer")

  a_rvfi_instr_obi_rdata_compressed:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     if_valid_i && id_ready_i && prefetch_compressed_if_i && (obi_instr_if.resp_payload.mpu_status == MPU_OK) |->
                     (prefetch_instr_if_i.bus_resp.rdata[15:0] == obi_instr_if.resp_payload.bus_resp.rdata[15:0]))
      else `uvm_error("rvfi", "rvfi_instr_obi compressed rdata does not track alignment buffer")

  a_rvfi_instr_obi_rdata_uncompressed:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     if_valid_i && id_ready_i && !prefetch_compressed_if_i && (obi_instr_if.resp_payload.mpu_status == MPU_OK) |->
                     (prefetch_instr_if_i.bus_resp.rdata[31:0] == obi_instr_if.resp_payload.bus_resp.rdata[31:0]))
      else `uvm_error("rvfi", "rvfi_instr_obi uncompressed rdata does not track alignment buffer")

  a_rvfi_instr_obi_err:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     if_valid_i && id_ready_i && (obi_instr_if.resp_payload.mpu_status == MPU_OK) |->
                     (prefetch_instr_if_i.bus_resp.err == obi_instr_if.resp_payload.bus_resp.err))
      else `uvm_error("rvfi", "rvfi_instr_obi err does not track alignment buffer")

  a_rvfi_instr_mpu_status:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     if_valid_i && id_ready_i |->
                     (prefetch_instr_if_i.mpu_status == obi_instr_if.resp_payload.mpu_status))
      else `uvm_error("rvfi", "rvfi_instr_obi mpu_status does not track alignment buffer")

  // Check that instructions fetched over two OBI transfers have the same OBI prot.
  // Ideally, this should be checked with a design assertion, but that is cumbersome since the aligmnent buffer interprets rdata to decide if an instruction is compressed or not.
  // By this time, the obi.prot for the given transfer(s) is no longer available.
  a_rvfi_instr_split_transfer_obi_prot:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     prefetch_valid_if_i && prefetch_ready_if_i && !prefetch_compressed_if_i && (prefetch_addr_if_i[1:0] != 2'b00 && (obi_instr_if.resp_payload.mpu_status == MPU_OK)) |->
                     obi_instr_fifo_q[obi_instr_rptr_q].req_payload.prot == obi_instr_fifo_q[obi_instr_rptr_q_inc].req_payload.prot)
      else `uvm_error("rvfi", "rvfi_instr_obi prot not the same for split transfers")


  // The following assertions and support logic check that memory transfers reported on rvfi_mem are consistent with LSU OBI transfers

  localparam int unsigned OBI_FIFO_SIZE = 32; // FIFO needs to be able to hold at least 2*13 memory transfers (because Zc can cause 13 transfers, and these can be split misaligned)
  localparam int unsigned MAX_NUM_MEMOP = 13; // This must be set to the maximum number of memory operations per retired instruction. If set too high it will result in unreachable covers

    typedef struct packed {
      bit               valid;
      bit               ld_str_blocked;
      bit [32*NMEM-1:0] addr;
      bit [ 4*NMEM-1:0] rmask;
      bit [ 4*NMEM-1:0] wmask;
      bit [32*NMEM-1:0] rdata;
      bit [32*NMEM-1:0] wdata;
      bit [ 1*NMEM-1:0] exokay;
      bit [ 1*NMEM-1:0] err;
      bit [ 3*NMEM-1:0] prot;
      bit [ 6*NMEM-1:0] atop;
      bit [ 2*NMEM-1:0] memtype;
      bit [ 1*NMEM-1:0] dbg;
    } rvfi_mem_t;

    // Return number of memory operations based on rvfi_mem_rmaks/wmask
    function automatic bit [$clog2(NMEM)-1:0] get_num_memop(bit [4*NMEM-1:0] rvfi_mem_mask);

      bit [$clog2(NMEM)-1:0] num_memop = 0;

      for (int i=0; i<NMEM; i++) begin
        if(|rvfi_mem_mask[i*4 +: 4]) begin
          num_memop++;
        end
      end

      return num_memop;
    endfunction : get_num_memop

    // Generate bitmask from byte-enables
    function automatic bit [31:0] get_bitmask(bit [3:0] be);
      bit [31:0] mask;
      mask[7:0]   = {8{be[0]}};
      mask[15:8]  = {8{be[1]}};
      mask[23:16] = {8{be[2]}};
      mask[31:24] = {8{be[3]}};
      return mask;
    endfunction : get_bitmask

    // Identify split tranfers based on address LSB's and be
    function automatic bit split_xfer(bit [1:0] addr_lsb, bit [3:0] be);
      if((addr_lsb + $countones(be)) > 4) begin
        return 1'b1;
      end
      else begin
        return 1'b0;
      end
    endfunction : split_xfer

    // Helper signals to identify reads and writes on RVFI
    bit [MAX_NUM_MEMOP-1:0] rvfi_mem_xfer;
    bit [MAX_NUM_MEMOP-1:0] rvfi_mem_read;
    bit [MAX_NUM_MEMOP-1:0] rvfi_mem_write;
    bit                     split_transfer;

    // OBI FIFOs and pointers
    obi_data_req_t  [OBI_FIFO_SIZE-1:0] data_obi_req_fifo;
    obi_data_resp_t [OBI_FIFO_SIZE-1:0] data_obi_resp_fifo;
    bit [$clog2(OBI_FIFO_SIZE)-1:0] rd_ptr, rd_ptr_inc, rd_ptr_n;
    bit [$clog2(OBI_FIFO_SIZE)-1:0] wr_req_ptr, wr_resp_ptr;

    // Indicate number of memory operations per instruction
    bit [$clog2(NMEM):0]                       num_memop;

    rvfi_mem_t rvfi_mem, rvfi_mem_dly, rvfi_mem_exp;

    assign rvfi_mem.valid = rvfi_valid;
    assign rvfi_mem.ld_str_blocked = rvfi_trap.trap && (
                                                        (rvfi_trap.exception &&
                                                         ((rvfi_trap.exception_cause == 6'h4) ||   // Load Address Misaligned
                                                          (rvfi_trap.exception_cause == 6'h5) ||   // Load Access Fault
                                                          (rvfi_trap.exception_cause == 6'h6) ||   // Store/AMO Address Misaligned
                                                          (rvfi_trap.exception_cause == 6'h7))) || // Store/AMO Access Fault
                                                        (rvfi_trap.debug &&
                                                         ((rvfi_trap.debug_cause == 3'h1) ||   // Debug Breakpoint
                                                          (rvfi_trap.debug_cause == 3'h2))));  // Debug trigger match

    assign rvfi_mem.addr    = rvfi_mem_addr;
    assign rvfi_mem.rmask   = rvfi_mem_rmask;
    assign rvfi_mem.wmask   = rvfi_mem_wmask;
    assign rvfi_mem.rdata   = rvfi_mem_rdata;
    assign rvfi_mem.wdata   = rvfi_mem_wdata;
    assign rvfi_mem.exokay  = rvfi_mem_exokay;
    assign rvfi_mem.err     = rvfi_mem_err;
    assign rvfi_mem.prot    = rvfi_mem_prot;
    assign rvfi_mem.atop    = rvfi_mem_atop;
    assign rvfi_mem.memtype = rvfi_mem_memtype;
    assign rvfi_mem.dbg     = rvfi_mem_dbg;

    localparam MAX_GNT_DLY = 2;

    bit [$clog2(MAX_GNT_DLY+1):0]   obi_gnt_dly_cnt;
    bit                             obi_gnt_delay_ok;

    // Keep track of cycles with obi request but no grant
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if(!rst_ni) begin
        obi_gnt_dly_cnt <= '0;
      end else begin
        if(m_c_obi_data_if.s_req.req && !m_c_obi_data_if.s_gnt.gnt) begin
          if (obi_gnt_dly_cnt <= MAX_GNT_DLY) begin
            obi_gnt_dly_cnt <= obi_gnt_dly_cnt + 1'b1;
          end
        end
        else begin
          obi_gnt_dly_cnt <= '0;
        end
      end
    end

    // Indicate that the OBI grant delay is small enough to allow the OBI FIFO to be populated
    // before rvfi_mem_dly.valid is set
    assign obi_gnt_delay_ok = obi_gnt_dly_cnt <= MAX_GNT_DLY;

    // Generate delayed version of rvfi_mem
    // Needed because write buffer can cause OBI tranfers to be accepted after it's signaled on RVFI
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if(!rst_ni) begin
        rvfi_mem_dly <= '0;
      end
      else begin
        rvfi_mem_dly <= $past(rvfi_mem, MAX_GNT_DLY-1);
      end
    end

  // FIFOs for OBI transfers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if(!rst_ni) begin
      data_obi_req_fifo  <= '0;
      data_obi_resp_fifo <= '0;
      wr_req_ptr  <= '0;
      wr_resp_ptr <= '0;
      rd_ptr      <= '0;
    end
    else begin

      // Update read pointer
      rd_ptr <= rd_ptr_n;

      // Populate OBI req FIFO
      if (m_c_obi_data_if.s_req.req && m_c_obi_data_if.s_gnt.gnt) begin
        data_obi_req_fifo[wr_req_ptr] <= m_c_obi_data_if.req_payload;
        wr_req_ptr <= wr_req_ptr + 1'b1;
      end

      // Populate OBI resp FIFO
      if (m_c_obi_data_if.s_rvalid.rvalid) begin
        data_obi_resp_fifo[wr_resp_ptr] <= m_c_obi_data_if.resp_payload;
        wr_resp_ptr <= wr_resp_ptr + 1'b1;
      end
    end
  end

  // Pointer to next OBI transfer. Used for split misaligned
  assign rd_ptr_inc = rd_ptr + 1'b1;

  // Extract number of memory operation in retired instruction
  assign num_memop = get_num_memop(rvfi_mem_dly.wmask) + get_num_memop(rvfi_mem_dly.rmask);

  // Assumption here is that if the first transfer is a split, the following ones will be as well.
  // The reasoning is that Zc push/pop will always do word read/writes, meaning that if the first is split, so will the rest
  assign split_transfer = split_xfer(rvfi_mem_dly.addr[1:0], rvfi_mem_dly.wmask[3:0] | rvfi_mem_dly.rmask[3:0]);

  // Increment read pointer based on memory operations in the retired instruction
  always_comb begin
    rd_ptr_n = rd_ptr;

    if (|rvfi_mem_xfer) begin
      if(split_transfer) begin
        // For split transfers, we'll consume 2 OBI tranfers per memory operation
        rd_ptr_n = rd_ptr + ($clog2(OBI_FIFO_SIZE))'(2*num_memop);
      end
      else begin
        rd_ptr_n = rd_ptr + ($clog2(OBI_FIFO_SIZE))'(1*num_memop);
      end
    end
  end

  // FIFO depth and assertions are designed to support up to MAX_NUM_MEMOP memory operations per retired instruction.
  // Make sure this assumption holds
  a_rvfi_mem_max_num_memop:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     |rvfi_mem_xfer |-> num_memop <= MAX_NUM_MEMOP)
        else `uvm_error("rvfi", "Memory operations > MAX_NUM_MEMOP. Potential overflow in SVA support logic.")

  genvar i_memop;
  generate

    for(i_memop = 0; i_memop < MAX_NUM_MEMOP; i_memop++) begin: rvfi_mem_asrt

      assign rvfi_mem_read[i_memop]  = rvfi_mem_dly.valid && (|rvfi_mem_dly.rmask[(4*i_memop) +: 4]);
      assign rvfi_mem_write[i_memop] = rvfi_mem_dly.valid && (|rvfi_mem_dly.wmask[(4*i_memop) +: 4]);
      assign rvfi_mem_xfer[i_memop]  = rvfi_mem_read[i_memop] || rvfi_mem_write[i_memop];

      // Helper signals
      bit [3:0]  exp_rvfi_mem_mask;
      bit [31:0] split_1st_wdata;
      bit [31:0] split_2nd_wdata;
      bit [31:0] split_1st_rdata;
      bit [31:0] split_2nd_rdata;
      bit        split_1st_err;
      bit        split_2nd_err;
      bit [2:0]  split_2nd_shift;

      bit [$clog2(OBI_FIFO_SIZE)-1:0] rd_ptr_memop, rd_ptr_memop_inc;

      // Assemble expected transaction on RVFI, based on OBI FIFO
      always_comb begin

        rvfi_mem_exp.addr    [32*i_memop +: 32] = '0;
        rvfi_mem_exp.rmask   [ 4*i_memop +:  4] = '0;
        rvfi_mem_exp.wmask   [ 4*i_memop +:  4] = '0;
        rvfi_mem_exp.rdata   [32*i_memop +: 32] = '0;
        rvfi_mem_exp.wdata   [32*i_memop +: 32] = '0;
        rvfi_mem_exp.exokay  [ 1*i_memop +:  1] = '0;
        rvfi_mem_exp.err     [ 1*i_memop +:  1] = '0;
        rvfi_mem_exp.prot    [ 3*i_memop +:  3] = '0;
        rvfi_mem_exp.atop    [ 6*i_memop +:  6] = '0;
        rvfi_mem_exp.memtype [ 2*i_memop +:  2] = '0;
        rvfi_mem_exp.dbg     [ 1*i_memop +:  1] = '0;

        exp_rvfi_mem_mask                    = '0;
        split_2nd_shift                      = '0;
        split_1st_wdata                      = '0;
        split_2nd_wdata                      = '0;
        split_1st_rdata                      = '0;
        split_2nd_rdata                      = '0;
        split_1st_err                        = '0;
        split_2nd_err                        = '0;

        rd_ptr_memop                         = '0;
        rd_ptr_memop_inc                     = '0;

        if (rvfi_mem_xfer[i_memop]) begin

          if(split_transfer) begin
            // Split misaligned transfer(s)

            rd_ptr_memop      = rd_ptr + ($clog2(OBI_FIFO_SIZE))'(2*i_memop); // Split transfers are reported in one memory operation on rvfi_mem, but results in 2 OBI transfers.
            rd_ptr_memop_inc  = rd_ptr_memop + 1'b1;

            split_2nd_shift   = 3'h4 - data_obi_req_fifo[rd_ptr_memop].addr[1:0];

            exp_rvfi_mem_mask = (data_obi_req_fifo[rd_ptr_memop].be     >> data_obi_req_fifo[rd_ptr_memop].addr[1:0]) |
                                (data_obi_req_fifo[rd_ptr_memop_inc].be << split_2nd_shift);

            // Extract data from the two OBI transfers
            split_1st_wdata    = data_obi_req_fifo[rd_ptr_memop].wdata     & get_bitmask(data_obi_req_fifo[rd_ptr_memop].be);
            split_2nd_wdata    = data_obi_req_fifo[rd_ptr_memop_inc].wdata & get_bitmask(data_obi_req_fifo[rd_ptr_memop_inc].be);

            split_1st_rdata    = data_obi_resp_fifo[rd_ptr_memop].rdata     & get_bitmask(data_obi_req_fifo[rd_ptr_memop].be);
            split_2nd_rdata    = data_obi_resp_fifo[rd_ptr_memop_inc].rdata & get_bitmask(data_obi_req_fifo[rd_ptr_memop_inc].be);

            split_1st_err    = data_obi_resp_fifo[rd_ptr_memop].err[0] && !data_obi_req_fifo[rd_ptr_memop].memtype[0];
            split_2nd_err    = data_obi_resp_fifo[rd_ptr_memop_inc].err[0] && !data_obi_req_fifo[rd_ptr_memop_inc].memtype[0];

            // Align rdata/wdata to correspond to expected rdata/wdata on RVFI
            rvfi_mem_exp.wdata[(32*i_memop) +: 32] = split_1st_wdata >> (8 * data_obi_req_fifo[rd_ptr_memop].addr[1:0]) |
                                                     split_2nd_wdata << (8 * split_2nd_shift);

            rvfi_mem_exp.rdata[(32*i_memop) +: 32] = split_1st_rdata >> (8 * data_obi_req_fifo[rd_ptr_memop].addr[1:0]) |
                                                     split_2nd_rdata << (8 * split_2nd_shift);

            rvfi_mem_exp.err[( 1*i_memop) +:  1] = split_1st_err | split_2nd_err;

          end
          else begin

            rd_ptr_memop                           = rd_ptr + ($clog2(OBI_FIFO_SIZE))'(i_memop);

            exp_rvfi_mem_mask                      = data_obi_req_fifo[rd_ptr_memop].be >> data_obi_req_fifo[rd_ptr_memop].addr[1:0];

            // Align rdata/wdata to correspond to expected rdata/wdata on RVFI
            rvfi_mem_exp.wdata[(32*i_memop) +: 32] = data_obi_req_fifo[rd_ptr_memop].wdata >> (8 * data_obi_req_fifo[rd_ptr_memop].addr[1:0]);

            rvfi_mem_exp.rdata[(32*i_memop) +: 32] = data_obi_resp_fifo[rd_ptr_memop].rdata >> (8 * data_obi_req_fifo[rd_ptr_memop].addr[1:0]);

            rvfi_mem_exp.err  [(1*i_memop) +:   1] = data_obi_resp_fifo[rd_ptr_memop].err[0] && !data_obi_req_fifo[rd_ptr_memop].memtype[0];

          end

          // Addr and prot are equal for both transfers in a split transfer
          rvfi_mem_exp.addr   [(32*i_memop) +: 32] = data_obi_req_fifo[rd_ptr_memop].addr;
          rvfi_mem_exp.prot   [(3*i_memop)  +: 3]  = data_obi_req_fifo[rd_ptr_memop].prot;
          rvfi_mem_exp.atop   [(6*i_memop)  +: 6]  = data_obi_req_fifo[rd_ptr_memop].atop;
          rvfi_mem_exp.memtype[(2*i_memop)  +: 2]  = data_obi_req_fifo[rd_ptr_memop].memtype;
          rvfi_mem_exp.dbg    [(1*i_memop)  +: 1]  = data_obi_req_fifo[rd_ptr_memop].dbg;
          rvfi_mem_exp.exokay [(1*i_memop)  +: 1]  = data_obi_resp_fifo[rd_ptr_memop].exokay && !data_obi_req_fifo[rd_ptr_memop].memtype[0];

          if(rvfi_mem_read[i_memop]) begin
            rvfi_mem_exp.rmask[(4*i_memop) +: 4] = exp_rvfi_mem_mask;
          end
          else begin
            rvfi_mem_exp.wmask[(4*i_memop) +: 4] = exp_rvfi_mem_mask;
          end

        end // if (rvfi_mem_xfer[i_memop])

      end

      // Assert that rvfi_mem is consistent with OBI transfers
      a_rvfi_mem_consistency_read_addr:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                     rvfi_mem_read[i_memop] |-> rvfi_mem_exp.addr[(32*i_memop) +: 32] == rvfi_mem_dly.addr[(32*i_memop) +: 32])
        else `uvm_error("rvfi", "rvfi_mem_addr not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_rmask:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                     rvfi_mem_read[i_memop] |-> rvfi_mem_exp.rmask[(4*i_memop) +: 4] == rvfi_mem_dly.rmask[(4*i_memop) +: 4])
        else `uvm_error("rvfi", "rvfi_mem_rmask not consistent with OBI transfers")

      a_rvfi_mem_consistency_rdata:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       rvfi_mem_read[i_memop] && !rvfi_mem_dly.ld_str_blocked |->
                       (rvfi_mem_exp.rdata[(32*i_memop) +: 32] & get_bitmask(rvfi_mem_exp.rmask[(4*i_memop) +: 4])) ==
                       (rvfi_mem_dly.rdata[(32*i_memop) +: 32] & get_bitmask(rvfi_mem_dly.rmask[(4*i_memop) +: 4])))
        else `uvm_error("rvfi", "rvfi_mem_rdata not consistent with OBI transfers")

      a_rvfi_mem_consistency_read_prot:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       rvfi_mem_read[i_memop] |-> rvfi_mem_exp.prot[(3*i_memop) +: 3] == rvfi_mem_dly.prot[(3*i_memop) +: 3])
        else `uvm_error("rvfi", "rvfi_mem_prot not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_atop:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        rvfi_mem_read[i_memop] |-> rvfi_mem_exp.atop[(6*i_memop) +: 6] == rvfi_mem_dly.atop[(6*i_memop) +: 6])
        else `uvm_error("rvfi", "rvfi_mem_atop not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_memtype:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        rvfi_mem_read[i_memop] |-> rvfi_mem_exp.memtype[(2*i_memop) +: 2] == rvfi_mem_dly.memtype[(2*i_memop) +: 2])
        else `uvm_error("rvfi", "rvfi_mem_memtype not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_dbg:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        rvfi_mem_read[i_memop] |-> rvfi_mem_exp.dbg[(1*i_memop) +: 1] == rvfi_mem_dly.dbg[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_dbg not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_exokay:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        rvfi_mem_read[i_memop] |-> rvfi_mem_exp.exokay[(1*i_memop) +: 1] == rvfi_mem_dly.exokay[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_exokay not consistent with OBI transfers for reads")

      a_rvfi_mem_consistency_read_err:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        rvfi_mem_read[i_memop] |-> rvfi_mem_exp.err[(1*i_memop) +: 1] == rvfi_mem_dly.err[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_err not consistent with OBI transfers for reads")


      a_rvfi_mem_consistency_write_addr:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                     obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.addr[(32*i_memop) +: 32] == rvfi_mem_dly.addr[(32*i_memop) +: 32])
        else `uvm_error("rvfi", "rvfi_mem_addr not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_wmask:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                     obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.wmask[(4*i_memop) +: 4] == rvfi_mem_dly.wmask[(4*i_memop) +: 4])
        else `uvm_error("rvfi", "rvfi_mem_wdata not consistent with OBI transfers")

      a_rvfi_mem_consistency_wdata:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                     obi_gnt_delay_ok && rvfi_mem_write[i_memop] |->
                       (rvfi_mem_exp.wdata[(32*i_memop) +: 32] & get_bitmask(rvfi_mem_exp.wmask[(4*i_memop) +: 4])) ==
                       (rvfi_mem_dly.wdata[(32*i_memop) +: 32] & get_bitmask(rvfi_mem_dly.wmask[(4*i_memop) +: 4])))
        else `uvm_error("rvfi", "rvfi_mem_wdata not consistent with OBI transfers")

      a_rvfi_mem_consistency_write_prot:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.prot[(3*i_memop) +: 3] == rvfi_mem_dly.prot[(3*i_memop) +: 3])
        else `uvm_error("rvfi", "rvfi_mem_prot not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_atop:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.atop[(6*i_memop) +: 6] == rvfi_mem_dly.atop[(6*i_memop) +: 6])
        else `uvm_error("rvfi", "rvfi_mem_atop not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_memtype:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                        obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.memtype[(2*i_memop) +: 2] == rvfi_mem_dly.memtype[(2*i_memop) +: 2])
        else `uvm_error("rvfi", "rvfi_mem_memtype not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_dbg:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.dbg[(1*i_memop) +: 1] == rvfi_mem_dly.dbg[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_dbg not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_exokay:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.exokay[(1*i_memop) +: 1] == rvfi_mem_dly.exokay[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_exokay not consistent with OBI transfers for writes")

      a_rvfi_mem_consistency_write_err:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       obi_gnt_delay_ok && rvfi_mem_write[i_memop] |-> rvfi_mem_exp.err[(1*i_memop) +: 1] == rvfi_mem_dly.err[(1*i_memop) +: 1])
        else `uvm_error("rvfi", "rvfi_mem_err not consistent with OBI transfers for writes")

    end

  endgenerate

endmodule
