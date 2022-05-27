// Copyright 202[x] Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.


////////////////////////////////////////////////////////////////////////////////
// Engineer:       Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    cv32e40x_controller_fsm                                 //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    FSM of the pipeline controller                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_controller_fsm import cv32e40x_pkg::*;
#(
  parameter bit       X_EXT           = 0,
  parameter bit       SMCLIC          = 0,
  parameter int       SMCLIC_ID_WIDTH = 5
)
(
  // Clocks and reset
  input  logic        clk,                        // Gated clock
  input  logic        clk_ungated_i,              // Ungated clock
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start executing

  // From bypass logic
  input  ctrl_byp_t   ctrl_byp_i,

  // From IF stage
  input logic [31:0]   pc_if_i,

  // From ID stage
  input  if_id_pipe_t if_id_pipe_i,
  input  logic        alu_jmp_id_i,               // Jump in ID
  input  logic        sys_mret_id_i,              // mret in ID
  input  logic        alu_en_id_i,                // alu_en qualifier for jumps
  input  logic        sys_en_id_i,                // sys_en qualifier for mret

  // From EX stage
  input  id_ex_pipe_t id_ex_pipe_i,
  input  logic        branch_decision_ex_i,       // branch decision signal from EX ALU
  input  logic        last_op_ex_i,               // EX stage contains the last operation of an instruction

  // From WB stage
  input  ex_wb_pipe_t ex_wb_pipe_i,
  input  logic [1:0]  lsu_err_wb_i,               // LSU caused bus_error in WB stage, gated with data_rvalid_i inside load_store_unit
  input  logic        last_op_wb_i,               // WB stage contains the last operation of an instruction

  // From LSU (WB)
  input  mpu_status_e lsu_mpu_status_wb_i,        // MPU status (WB timing)
  input  logic        data_stall_wb_i,            // WB stalled by LSU

  input  logic        lsu_busy_i,                 // LSU is busy with outstanding transfers

  input  logic        lsu_interruptible_i,        // LSU can be interrupted
  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,             // irq requst
  input  logic [9:0]  irq_id_ctrl_i,              // irq id
  input  logic        irq_wu_ctrl_i,              // irq wakeup control
  input  logic        irq_clic_shv_i,             // CLIC mode selective hardware vectoring
  input  logic [7:0]  irq_clic_level_i,           // CLIC mode current interrupt level

  // From cs_registers
  input  logic  [1:0] mtvec_mode_i,
  input  dcsr_t       dcsr_i,

  // Toplevel input
  input  logic        debug_req_i,                // External debug request

  // All controller FSM outputs
  output ctrl_fsm_t   ctrl_fsm_o,

  // Stage valid/ready signals
  input  logic        if_valid_i,       // IF stage has valid (non-bubble) data for next stage
  input  logic        id_ready_i,       // ID stage is ready for new data
  input  logic        id_valid_i,       // ID stage has valid (non-bubble) data for next stage
  input  logic        ex_ready_i,       // EX stage is ready for new data
  input  logic        ex_valid_i,       // EX stage has valid (non-bubble) data for next stage
  input  logic        wb_ready_i,       // WB stage is ready for new data,
  input  logic        wb_valid_i,       // WB stage ha valid (non-bubble) data

  // Fencei flush handshake
  output logic        fencei_flush_req_o,
  input logic         fencei_flush_ack_i,

  // Data OBI interface monitor
  if_c_obi.monitor     m_c_obi_data_if,

  // eXtension interface
  if_xif.cpu_commit    xif_commit_if,
  input                xif_csr_error_i
);

   // FSM state encoding
  ctrl_state_e ctrl_fsm_cs, ctrl_fsm_ns;

  // Debug state
  debug_state_e debug_fsm_cs, debug_fsm_ns;

  // Sticky version of debug_req_i
  logic debug_req_q;

  // Sticky version of lsu_err_wb_i
  logic nmi_pending_q;
  logic nmi_is_store_q; // 1 for store, 0 for load

  // Debug mode
  logic debug_mode_n;
  logic debug_mode_q;

  // Signals used for halting IF after first instruction
  // during single step
  logic single_step_halt_if_n;
  logic single_step_halt_if_q; // Halting IF after issuing one insn in single step mode

  // ID signals
  logic sys_mret_id;             // MRET in ID
  logic jmp_id;                  // JAL, JALR in ID
  logic jump_in_id;
  logic jump_taken_id;

  // EX signals
  logic branch_in_ex;
  logic branch_taken_ex;

  logic branch_taken_n;
  logic branch_taken_q;

  // WB signals
  logic exception_in_wb;
  logic [10:0] exception_cause_wb;
  logic wfi_in_wb;
  logic fencei_in_wb;
  logic mret_in_wb;
  logic dret_in_wb;
  logic ebreak_in_wb;
  logic trigger_match_in_wb;
  logic xif_in_wb;

  logic pending_nmi;
  logic pending_nmi_early;
  logic pending_debug;
  logic pending_single_step;
  logic pending_single_step_ptr;
  logic pending_interrupt;

  // Flags for allowing interrupt and debug
  logic exception_allowed;
  logic interrupt_allowed;
  logic nmi_allowed;
  logic debug_allowed;
  logic single_step_allowed;

  // Flag indicating there is a 'live' CLIC pointer in the pipeline
  // Used to block debug until pointer
  logic pointer_in_pipeline;

  // Internal irq_ack for use when a (clic) pointer reaches ID stage and
  // we have single stepping enabled.
  logic non_shv_irq_ack;

  // Flops for debug cause
  logic [2:0] debug_cause_n;
  logic [2:0] debug_cause_q;

  logic [10:0] exc_cause; // id of taken interrupt. Max width, unused bits are tied off.

  logic       fencei_ready;
  logic       fencei_flush_req_set;
  logic       fencei_req_and_ack_q;
  logic       fencei_ongoing;

  // Pipeline PC mux control
  pipe_pc_mux_e pipe_pc_mux_ctrl;

  // Flag for signalling that a new instruction arrived in WB.
  // Used for performance counters. High for one cycle, unless WB is halted
  // (for fence.i for example), then it will remain high until un-halted.
  logic       wb_counter_event;

  // Gated version of wb_counter_event
  // Do not count if halted or killed
  logic       wb_counter_event_gated;

  // Detect uninterruptible table jumps
  logic       tbljmp_in_ex_wb;

  assign fencei_ready = !lsu_busy_i;

  // Once the fencei handshake is initiated, it must complete and the instruction must retire.
  // The instruction retires when fencei_req_and_ack_q = 1
  assign fencei_ongoing = fencei_flush_req_o || fencei_req_and_ack_q;

  // Mux selector for vectored IRQ PC
  // Used for both basic mode and CLIC when shv == 0.
  assign ctrl_fsm_o.mtvec_pc_mux = ((mtvec_mode_i == 2'b0) || ((mtvec_mode_i == 2'b11) && !irq_clic_shv_i)) ? 5'h0 : exc_cause[4:0];

  // CLIC mode vectored PC mux is always the same as exc_cause.
  assign ctrl_fsm_o.mtvt_pc_mux = exc_cause[9:0];

  // Mux selector for table jumps
  // index for table jumps taken from instruction word in ID stage.
  assign ctrl_fsm_o.jvt_pc_mux = if_id_pipe_i.instr.bus_resp.rdata[19:12];


  ////////////////////////////////////////////////////////////////////
  // ID stage

  // A jump is taken in ID for jump instructions, and also for mret instructions
  // Checking validity of jump/mret instruction with if_id_pipe_i.instr_valid and the respective alu_en/sys_en.
  // Using the ID stage local instr_valid would bring halt_id and kill_id into the equation
  // causing a path from data_rvalid to instr_addr_o/instr_req_o/instr_memtype_o via pc_set.



  assign sys_mret_id = sys_en_id_i && sys_mret_id_i && if_id_pipe_i.instr_valid;
  assign jmp_id      = alu_en_id_i && alu_jmp_id_i  && if_id_pipe_i.instr_valid;

  // Detect that a jump is in the ID stage.
  // This will also be true for table jumps, as they are encoded as JAL instructions.
  //   An extra table jump flag is used in the logic for taken jumps to disinguish between
  //   regular jumps and table jumps.
  // Table jumps do an implicit read of the JVT CSR, so csr_stall must be accounted for.
  assign jump_in_id = (jmp_id && !if_id_pipe_i.instr_meta.tbljmp && !ctrl_byp_i.jalr_stall) ||
                      (jmp_id &&  if_id_pipe_i.instr_meta.tbljmp && !ctrl_byp_i.csr_stall ) ||
                      (sys_mret_id && !ctrl_byp_i.csr_stall);

  // Blocking on branch_taken_q, as a jump has already been taken
  assign jump_taken_id = jump_in_id && !branch_taken_q;

 // todo: RVFI does not use jump_taken_id (which is not in itself an issue); we should have an assertion showing that the target address remains constant during jump_in_id; same remark for branches

  // EX stage
  // Branch taken for valid branch instructions in EX with valid decision

  assign branch_in_ex = id_ex_pipe_i.alu_bch && id_ex_pipe_i.alu_en && id_ex_pipe_i.instr_valid && branch_decision_ex_i;

  // Blocking on branch_taken_q, as a branch ha already been taken
  assign branch_taken_ex = branch_in_ex && !branch_taken_q;

  // Exception in WB if the following evaluates to 1
  assign exception_in_wb = ((ex_wb_pipe_i.instr.mpu_status != MPU_OK)                              ||
                             ex_wb_pipe_i.instr.bus_resp.err                                       ||
                            ex_wb_pipe_i.illegal_insn                                              ||
                            (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_ecall_insn)                   ||
                            (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_ebrk_insn)                    ||
                            (lsu_mpu_status_wb_i != MPU_OK)) && ex_wb_pipe_i.instr_valid;

  // Set exception cause
  assign exception_cause_wb = (ex_wb_pipe_i.instr.mpu_status != MPU_OK)                  ? EXC_CAUSE_INSTR_FAULT     :
                              ex_wb_pipe_i.instr.bus_resp.err                            ? EXC_CAUSE_INSTR_BUS_FAULT :
                              ex_wb_pipe_i.illegal_insn                                  ? EXC_CAUSE_ILLEGAL_INSN    :
                              (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_ecall_insn)       ? EXC_CAUSE_ECALL_MMODE     :
                              (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_ebrk_insn)        ? EXC_CAUSE_BREAKPOINT      :
                              (lsu_mpu_status_wb_i == MPU_WR_FAULT)                      ? EXC_CAUSE_STORE_FAULT     :
                              EXC_CAUSE_LOAD_FAULT; // (lsu_mpu_status_wb_i == MPU_RE_FAULT)

  // For now we are always allowed to take exceptions once they arrive in WB.
  // For a misaligned load/store with MPU error on the first half, the second half
  // will arrive in EX when the first half (with error) arrives in WB. The exception will
  // be taken and the bus transaction of the second half will be suppressed by the ctrl_fsm_o.kill_ex signal.
  // The only higher priority events are  NMI, debug and interrupts, and none of them are allowed if there is
  // a load/store in WB.
  assign exception_allowed = 1'b1;

  // wfi in wb
  assign wfi_in_wb = ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_wfi_insn && ex_wb_pipe_i.instr_valid;

  // fencei in wb
  assign fencei_in_wb = ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_fencei_insn && ex_wb_pipe_i.instr_valid;

  // mret in wb
  assign mret_in_wb = ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_mret_insn && ex_wb_pipe_i.instr_valid;

  // dret in wb
  assign dret_in_wb = ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_dret_insn && ex_wb_pipe_i.instr_valid;

  // ebreak in wb
  assign ebreak_in_wb = ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_ebrk_insn && ex_wb_pipe_i.instr_valid;

  // Trigger match in wb
  // Trigger_match during debug mode is masked in the trigger logic inside cs_registers.sv
  assign trigger_match_in_wb = (ex_wb_pipe_i.trigger_match && ex_wb_pipe_i.instr_valid);

  // An offloaded instruction is in WB
  assign xif_in_wb = (ex_wb_pipe_i.xif_en && ex_wb_pipe_i.instr_valid);

  // Pending NMI
  // Using flopped version to avoid paths from data_err_i/data_rvalid_i to instr_* outputs
  // Gating the pending signal instead of the allowed signal for debug related conditions, otherwise a pending NMI during debug mode
  // or single stepping with dcsr.stepie==0 would stall ID stage and we would never get out of debug, resulting in a deadlock.
  assign pending_nmi = nmi_pending_q && !debug_mode_q && !(dcsr_i.step && !dcsr_i.stepie);

  // Early version of the pending_nmi signal, using the unflopped lsu_err_wb_i[0]
  // This signal is used for halting the ID stage in the same cycle as the bus error arrives.
  // This ensures that any instruction in the ID stage that may depend on the result of the faulted load
  // will not propagate to the EX stage. For cycles after lsu_err_wb_i[0] is
  // high, ID stage will be halted due to pending_nmi and !nmi_allowed.
  assign pending_nmi_early =  lsu_err_wb_i[0] && !debug_mode_q && !(dcsr_i.step && !dcsr_i.stepie);

  // todo: Halting ID and killing it later will not work for Zce (push/pop)

  // dcsr.nmip will always see a pending nmi if nmi_pending_q is set.
  // This CSR bit shall not be gated by debug mode or step without stepie
  assign ctrl_fsm_o.pending_nmi = nmi_pending_q;

  // Debug //

  // Single step will need to finish insn in WB, including LSU
  // LSU will now set valid_1_o only for second part of misaligned instructions.
  // We can always allow single step when checking for wb_valid_i in 'pending_single_step'
  // - no other instructions should be in the pipeline.
  assign single_step_allowed = 1'b1;

  /*
  Debug spec 1.0.0 (unratified as of Aug 9th '21)
  "If control is transferred to a trap handler while executing the instruction, then Debug Mode is
  re-entered immediately after the PC is changed to the trap handler, and the appropriate tval and
  cause registers are updated. In this case none of the trap handler is executed, and if the cause was
  a pending interrupt no instructions might be executed at all."

  Hence, a pending_single_step is asserted if we take an interrupt when we should be stepping.
  For any interruptible instructions (non-LSU), at any stage, we would kill the instruction and jump
  to debug mode without executing any instructions. Interrupt handler's first instruction will be in dpc.

  For LSU instructions that may not be killed (if they reach WB of stay in EX for >1 cycles),
  we are not allowed to take interrupts, and we will re-enter debug mode after finishing the LSU.
  Interrupt will then be taken when we enter the next step.
  */

  assign non_shv_irq_ack = ctrl_fsm_o.irq_ack && !irq_clic_shv_i;

  // single step becomes pending when the last operation of an instruction is done in WB, or we ack a non-shv interrupt.
  assign pending_single_step = (!debug_mode_q && dcsr_i.step && ((wb_valid_i && last_op_wb_i) || non_shv_irq_ack)) && !pending_debug;

  // Separate flag for pending single step when doing CLIC SHV, evaluated while in POINTER_FETCH stage
  assign pending_single_step_ptr = !debug_mode_q && dcsr_i.step && (wb_valid_i || 1'b1) && !pending_debug;


  // Detect if there is a live CLIC pointer in the pipeline
  // This should block debug
  generate
    if(SMCLIC) begin : gen_clic_pointer_flag
      // We only need to check EX and WB, as the FSM will only be in FUNCTIONAL state
      // one cycle after the target CLIC jump has been performed from ID
      assign pointer_in_pipeline = (id_ex_pipe_i.instr_valid && id_ex_pipe_i.instr_meta.clic_ptr) ||
                                   (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.instr_meta.clic_ptr);
    end else begin : gen_basic_pointer_flag
      assign pointer_in_pipeline = 1'b0;
    end
  endgenerate
  // Regular debug will kill insn in WB, do not allow if LSU is not interruptible, a fence.i handshake is taking place
  // or if an offloaded instruction is in WB.
  // LSU will not be interruptible if the outstanding counter != 0, or
  // a trans_valid has been clocked without ex_valid && wb_ready handshake.
  // The cycle after fencei enters WB, the fencei handshake will be initiated. This must complete and the fencei instruction must retire before allowing debug.
  // Once the first part of a table jump has finished in WB, we are not allowed to take debug before the last part finishes. This can be detected when the last
  // part of a table jump is in either EX or WB.
  assign debug_allowed = lsu_interruptible_i && !fencei_ongoing && !xif_in_wb && !pointer_in_pipeline && !tbljmp_in_ex_wb;

  // Debug pending for any other reason than single step
  assign pending_debug = (trigger_match_in_wb) ||
                         ((debug_req_i || debug_req_q) && !debug_mode_q)   || // External request
                         (ebreak_in_wb && dcsr_i.ebreakm && !debug_mode_q) || // Ebreak with dcsr.ebreakm==1
                         (ebreak_in_wb && debug_mode_q); // Ebreak during debug_mode restarts execution from dm_halt_addr, as a regular debug entry without CSR updates.

  // Determine cause of debug
  // pending_single_step may only happen if no other causes for debug are true.
  // The flopped version of this is checked during DEBUG_TAKEN state (one cycle delay)
  assign debug_cause_n = pending_single_step ? DBG_CAUSE_STEP :
                         pending_single_step_ptr ? DBG_CAUSE_STEP :
                         trigger_match_in_wb ? DBG_CAUSE_TRIGGER :
                         (ebreak_in_wb && dcsr_i.ebreakm && !debug_mode_q) ? DBG_CAUSE_EBREAK :
                         DBG_CAUSE_HALTREQ;

  // Debug cause to CSR from flopped version (valid during DEBUG_TAKEN)
  assign ctrl_fsm_o.debug_cause = debug_cause_q;

  // interrupt may be pending from the int_controller even though we are in debug mode.
  // Gating the pending signal instead of the allowed signal for debug related conditions, otherwise a pending interrupt during debug mode
  // or single stepping with dcsr.stepie==0 would stall ID stage and we would never get out of debug, resulting in a deadlock.
  assign pending_interrupt = irq_req_ctrl_i && !debug_mode_q && !(dcsr_i.step && !dcsr_i.stepie);

  // Table jumps may not be interrupted if the last part has reached EX or WB.
  assign tbljmp_in_ex_wb = ((id_ex_pipe_i.instr_meta.tbljmp && id_ex_pipe_i.last_op) || (ex_wb_pipe_i.instr_meta.tbljmp && ex_wb_pipe_i.last_op));

  // Allow interrupts to be taken only if there is no data request in WB,
  // and no trans_valid has been clocked from EX to environment.
  // Offloaded instructions in WB also block, as they cannot be killed after commit_kill=0 (EX stage)
  // LSU instructions which were suppressed due to previous exceptions or trigger match
  // will be interruptable as they were convered to NOP in ID stage.
  // The cycle after fencei enters WB, the fencei handshake will be initiated. This must complete and the fencei instruction must retire before allowing interrupts.
  // TODO:OK:low May allow interuption of Zce to idempotent memories
  // Once the first part of a table jump has finished in WB, we are not allowed to take interrupts before the last part finishes. This can be detected when the last
  // part of a table jump is in either EX or WB.

  assign interrupt_allowed = lsu_interruptible_i && !fencei_ongoing && !xif_in_wb && !tbljmp_in_ex_wb;

  // Allowing NMI's follow the same rule as regular interrupts.
  assign nmi_allowed = interrupt_allowed;

  // Do not count if we have an exception in WB, trigger match in WB (we do not execute the instruction at trigger address),
  // or WB stage is killed or halted.
  // When WB is halted, we do not know (yet) if the instruction will retire or get killed.
  // Halted WB due to debug will result in WB getting killed
  // Halted WB due to fence.i will result in fence.i retire after handshake is done and we count when WB is un-halted
  assign wb_counter_event_gated = wb_counter_event && !exception_in_wb && !trigger_match_in_wb &&
                                  !ctrl_fsm_o.kill_wb && !ctrl_fsm_o.halt_wb;

  // Performance counter events
  assign ctrl_fsm_o.mhpmevent.minstret      = wb_counter_event_gated;
  assign ctrl_fsm_o.mhpmevent.compressed    = wb_counter_event_gated && ex_wb_pipe_i.instr_meta.compressed;
  assign ctrl_fsm_o.mhpmevent.jump          = wb_counter_event_gated && ex_wb_pipe_i.alu_jmp_qual;
  assign ctrl_fsm_o.mhpmevent.branch        = wb_counter_event_gated && ex_wb_pipe_i.alu_bch_qual;
  assign ctrl_fsm_o.mhpmevent.branch_taken  = wb_counter_event_gated && ex_wb_pipe_i.alu_bch_taken_qual;
  assign ctrl_fsm_o.mhpmevent.intr_taken    = ctrl_fsm_o.irq_ack;
  assign ctrl_fsm_o.mhpmevent.data_read     = m_c_obi_data_if.s_req.req && m_c_obi_data_if.s_gnt.gnt && !m_c_obi_data_if.req_payload.we;
  assign ctrl_fsm_o.mhpmevent.data_write    = m_c_obi_data_if.s_req.req && m_c_obi_data_if.s_gnt.gnt && m_c_obi_data_if.req_payload.we;
  assign ctrl_fsm_o.mhpmevent.if_invalid    = !if_valid_i && id_ready_i;
  assign ctrl_fsm_o.mhpmevent.id_invalid    = !id_valid_i && ex_ready_i;
  assign ctrl_fsm_o.mhpmevent.ex_invalid    = !ex_valid_i && wb_ready_i;
  assign ctrl_fsm_o.mhpmevent.wb_invalid    = !(wb_valid_i && last_op_wb_i);
  assign ctrl_fsm_o.mhpmevent.id_jalr_stall = ctrl_byp_i.jalr_stall && !id_valid_i && ex_ready_i;
  assign ctrl_fsm_o.mhpmevent.id_ld_stall   = ctrl_byp_i.load_stall && !id_valid_i && ex_ready_i;
  assign ctrl_fsm_o.mhpmevent.wb_data_stall = data_stall_wb_i;

  // Mux used to select PC from the different pipeline stages
  always_comb begin

    ctrl_fsm_o.pipe_pc = PC_WB;

    unique case (pipe_pc_mux_ctrl)
      PC_WB: ctrl_fsm_o.pipe_pc = ex_wb_pipe_i.pc;
      PC_EX: ctrl_fsm_o.pipe_pc = id_ex_pipe_i.pc;
      PC_ID: ctrl_fsm_o.pipe_pc = if_id_pipe_i.pc;
      PC_IF: ctrl_fsm_o.pipe_pc = pc_if_i;
      default:;
    endcase
  end

  //////////////
  // FSM comb //
  //////////////
  always_comb begin
    // Default values
    ctrl_fsm_ns = ctrl_fsm_cs;
    ctrl_fsm_o.ctrl_busy = 1'b1;
    ctrl_fsm_o.instr_req = 1'b1;

    ctrl_fsm_o.pc_mux    = PC_BOOT;
    ctrl_fsm_o.pc_set    = 1'b0;

    ctrl_fsm_o.irq_ack = 1'b0;
    ctrl_fsm_o.irq_id  = '0;
    ctrl_fsm_o.irq_level = '0;
    ctrl_fsm_o.dbg_ack = 1'b0;

    // IF stage is halted if an instruction has been issued during single step
    // to avoid more than one instructions passing down the pipe.
    ctrl_fsm_o.halt_if = single_step_halt_if_q;
    // ID stage is halted for regular stalls (i.e. stalls for which the instruction
    // currently in ID is not ready to be issued yet). Also halted if interrupt or debug pending
    // but not allowed to be taken. This is to create an interruptible bubble in WB.
    ctrl_fsm_o.halt_id = ctrl_byp_i.jalr_stall || ctrl_byp_i.load_stall || ctrl_byp_i.csr_stall || ctrl_byp_i.wfi_stall || ctrl_byp_i.mnxti_stall ||
                         (pending_interrupt && !interrupt_allowed) ||
                         (pending_debug && !debug_allowed) ||
                         (pending_nmi && !nmi_allowed) ||
                         (pending_nmi_early);
    // Halting EX if minstret_stall occurs. Otherwise we would read the wrong minstret value
    // Also halting EX if an offloaded instruction in WB may cause an exception, such that a following offloaded
    // instruction can correctly receive commit_kill.
    ctrl_fsm_o.halt_ex = ctrl_byp_i.minstret_stall || ctrl_byp_i.xif_exception_stall;
    ctrl_fsm_o.halt_wb = 1'b0;

    // By default no stages are killed
    ctrl_fsm_o.kill_if = 1'b0;
    ctrl_fsm_o.kill_id = 1'b0;
    ctrl_fsm_o.kill_ex = 1'b0;
    ctrl_fsm_o.kill_wb = 1'b0;

    ctrl_fsm_o.csr_restore_mret    = 1'b0;
    ctrl_fsm_o.csr_save_cause      = 1'b0;
    ctrl_fsm_o.csr_cause           = 32'h0;
    ctrl_fsm_o.csr_clear_minhv     = 1'b0;

    pipe_pc_mux_ctrl               = PC_WB;

    exc_cause                      = 11'b0;

    debug_mode_n                   = debug_mode_q;
    ctrl_fsm_o.debug_csr_save      = 1'b0;
    ctrl_fsm_o.block_data_addr     = 1'b0;

    // Single step halting of IF
    single_step_halt_if_n = single_step_halt_if_q;

    // Ensure jumps and branches are taken only once
    branch_taken_n                 = branch_taken_q;

    fencei_flush_req_set           = 1'b0;

    ctrl_fsm_o.pc_set_clicv        = 1'b0;
    ctrl_fsm_o.pc_set_tbljmp       = 1'b0;
    unique case (ctrl_fsm_cs)
      RESET: begin
        ctrl_fsm_o.instr_req = 1'b0;
        if (fetch_enable_i) begin
          ctrl_fsm_ns = BOOT_SET;
        end
      end
      // BOOT_SET state required to prevent (timing) path from
      // fetch_enable_i via pc_set to instruction interface outputs
      BOOT_SET: begin
        ctrl_fsm_o.instr_req = 1'b1;
        ctrl_fsm_o.pc_mux    = PC_BOOT;
        ctrl_fsm_o.pc_set    = 1'b1;
        ctrl_fsm_ns = FUNCTIONAL;
      end
      FUNCTIONAL: begin
        // NMI
        if (pending_nmi && nmi_allowed) begin
          ctrl_fsm_o.kill_if = 1'b1;
          ctrl_fsm_o.kill_id = 1'b1;
          ctrl_fsm_o.kill_ex = 1'b1;
          ctrl_fsm_o.kill_wb = 1'b1;

          ctrl_fsm_o.pc_set = 1'b1;
          ctrl_fsm_o.pc_mux = PC_TRAP_NMI;

          ctrl_fsm_o.csr_save_cause  = 1'b1;
          ctrl_fsm_o.csr_cause.irq = 1'b1;
          ctrl_fsm_o.csr_cause.exception_code = nmi_is_store_q ? INT_CAUSE_LSU_STORE_FAULT : INT_CAUSE_LSU_LOAD_FAULT;

          // Save pc from oldest valid instruction
          if (ex_wb_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_WB;
          end else if (id_ex_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_EX;
          end else if (if_id_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_ID;
          end else begin
            // IF PC will always be valid as it points to the next
            // instruction to be issued from IF to ID.
            pipe_pc_mux_ctrl = PC_IF;
          end

        // Debug entry (except single step which is handled later)
        end else if (pending_debug && debug_allowed) begin
          // Halt the whole pipeline
          ctrl_fsm_o.halt_if = 1'b1;
          ctrl_fsm_o.halt_id = 1'b1;
          ctrl_fsm_o.halt_ex = 1'b1;
          ctrl_fsm_o.halt_wb = 1'b1;

          ctrl_fsm_ns = DEBUG_TAKEN;
        // IRQ
        end else if (pending_interrupt && interrupt_allowed) begin
          ctrl_fsm_o.kill_if = 1'b1;
          ctrl_fsm_o.kill_id = 1'b1;
          ctrl_fsm_o.kill_ex = 1'b1;
          ctrl_fsm_o.kill_wb = 1'b1;

          ctrl_fsm_o.pc_set = 1'b1;

          exc_cause = {1'b0, irq_id_ctrl_i};

          ctrl_fsm_o.irq_ack = 1'b1;
          ctrl_fsm_o.irq_id  = irq_id_ctrl_i;

          ctrl_fsm_o.csr_save_cause  = 1'b1;
          ctrl_fsm_o.csr_cause.irq = 1'b1;


          if (SMCLIC) begin
            ctrl_fsm_o.csr_cause.exception_code = {1'b0, irq_id_ctrl_i};
            ctrl_fsm_o.irq_level = irq_clic_level_i;
            if (irq_clic_shv_i) begin
              ctrl_fsm_o.pc_mux = PC_TRAP_CLICV;
              ctrl_fsm_ns = POINTER_FETCH;
              ctrl_fsm_o.pc_set_clicv = 1'b1;
              ctrl_fsm_o.csr_cause.minhv = 1'b1;
            end else begin
              ctrl_fsm_o.pc_mux = PC_TRAP_IRQ;
            end
          end else begin
            ctrl_fsm_o.pc_mux = PC_TRAP_IRQ;
            ctrl_fsm_o.csr_cause.exception_code = {1'b0, irq_id_ctrl_i};
          end

          // Save pc from oldest valid instruction
          if (ex_wb_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_WB;
          end else if (id_ex_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_EX;
          end else if (if_id_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_ID;
          end else begin
            // IF PC will always be valid as it points to the next
            // instruction to be issued from IF to ID.
            pipe_pc_mux_ctrl = PC_IF;
          end

        end else begin
          if (exception_in_wb && exception_allowed) begin
            // Kill all stages
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            ctrl_fsm_o.kill_wb = 1'b0; // All write enables are suppressed, no need to kill WB.

            // Set pc to exception handler
            ctrl_fsm_o.pc_set = 1'b1;
            ctrl_fsm_o.pc_mux = debug_mode_q ? PC_TRAP_DBE : PC_TRAP_EXC;

            // Save CSR from WB
            pipe_pc_mux_ctrl = PC_WB;
            ctrl_fsm_o.csr_save_cause = !debug_mode_q; // Do not update CSRs if in debug mode
            ctrl_fsm_o.csr_cause.exception_code = exception_cause_wb;
          // Special insn
          end else if (wfi_in_wb) begin
            // Not halting EX/WB to allow insn (interruptible bubble) in EX to pass to WB before sleeping
            ctrl_fsm_o.halt_if = 1'b1;
            ctrl_fsm_o.halt_id = 1'b1; // Ensures second bubble after WFI (EX is empty while in SLEEP)
            ctrl_fsm_o.instr_req = 1'b0;
            ctrl_fsm_ns = SLEEP;
          end else if (fencei_in_wb) begin

            // Halt the pipeline
            ctrl_fsm_o.halt_if = 1'b1;
            ctrl_fsm_o.halt_id = 1'b1;
            ctrl_fsm_o.halt_ex = 1'b1;
            ctrl_fsm_o.halt_wb = 1'b1;

            if (fencei_ready) begin
              // Set fencei_flush_req_o in the next cycle
              fencei_flush_req_set = 1'b1;
            end
            if (fencei_req_and_ack_q) begin
              // fencei req and ack were set at in the same cycle, complete handshake and jump to PC_FENCEI

              // Unhalt wb, kill if,id,ex
              ctrl_fsm_o.kill_if   = 1'b1;
              ctrl_fsm_o.kill_id   = 1'b1;
              ctrl_fsm_o.kill_ex   = 1'b1;
              ctrl_fsm_o.halt_wb   = 1'b0;

              // Jump to PC from oldest valid instruction, excluding WB stage
              if (id_ex_pipe_i.instr_valid) begin
                pipe_pc_mux_ctrl = PC_EX;
              end else if (if_id_pipe_i.instr_valid) begin
                pipe_pc_mux_ctrl = PC_ID;
              end else begin
                pipe_pc_mux_ctrl = PC_IF;
              end

              ctrl_fsm_o.pc_set    = 1'b1;
              ctrl_fsm_o.pc_mux    = PC_FENCEI;

              fencei_flush_req_set = 1'b0;
            end
          end else if (dret_in_wb) begin
            // dret takes jump from WB stage
            // Kill previous stages and jump to pc in dpc
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;

            ctrl_fsm_o.pc_mux  = PC_DRET;
            ctrl_fsm_o.pc_set  = 1'b1;

            single_step_halt_if_n = 1'b0;
            debug_mode_n  = 1'b0;

          end else if (branch_taken_ex) begin
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;

            ctrl_fsm_o.pc_mux  = PC_BRANCH;
            ctrl_fsm_o.pc_set  = 1'b1;

            // Set flag to avoid further branches to the same target
            // if we are stalled
            branch_taken_n     = 1'b1;

          end else if (jump_taken_id) begin
            // Jumps in ID (JAL, JALR, mret)

            // kill_if
            ctrl_fsm_o.kill_if = 1'b1;

            if (sys_mret_id) begin
              ctrl_fsm_o.pc_mux = debug_mode_q ? PC_TRAP_DBE : PC_MRET;
              ctrl_fsm_o.pc_set = 1'b1;
              // Todo: if mcause.minhv
              //       halt ID until EX and WB are empty
              //       - pc_set_clicv
              //       state -> POINTER_FETCH

            end else begin
              // For table jumps we have two different jumps
              // - First part does a pointer fetch from (jvt + (index<<2))
              // - Second part jumps to the fetched pointer
              // Regular jumps use the regular jump to the target calculated in the ID stage.
              ctrl_fsm_o.pc_mux        = if_id_pipe_i.instr_meta.tbljmp && !if_id_pipe_i.last_op ? PC_TBLJUMP :
                                         if_id_pipe_i.instr_meta.tbljmp && if_id_pipe_i.last_op  ? PC_POINTER : PC_JUMP;
              ctrl_fsm_o.pc_set        = 1'b1;
              ctrl_fsm_o.pc_set_tbljmp = if_id_pipe_i.instr_meta.tbljmp && !if_id_pipe_i.last_op;
            end

            // Set flag to avoid further jumps to the same target
            // if we are stalled
            branch_taken_n = 1'b1;
          end

          // Mret in WB restores CSR regs
          //
          if (mret_in_wb && !ctrl_fsm_o.kill_wb) begin
            ctrl_fsm_o.csr_restore_mret  = !debug_mode_q;
          end
        end // !debug or interrupts

        // Single step debug entry
          // Need to be after (in parallell with) exception/interrupt handling
          // to ensure mepc and if_pc set correctly for use in dpc,
          // and to ensure only one instruction can retire during single step
        if (pending_single_step) begin
          if (single_step_allowed) begin
            ctrl_fsm_ns = DEBUG_TAKEN;
          end
        end
      end
      SLEEP: begin
        // There should be a bubble in EX and WB in this state (checked by assertion)
        // We are avoiding that a load/store starts its bus transaction
        ctrl_fsm_o.ctrl_busy = 1'b0;
        ctrl_fsm_o.instr_req = 1'b0;
        ctrl_fsm_o.halt_wb   = 1'b1; // Put backpressure on pipeline to avoid retiring following instructions
        if (ctrl_fsm_o.wake_from_sleep) begin
          ctrl_fsm_ns = FUNCTIONAL;
          ctrl_fsm_o.ctrl_busy = 1'b1;
        end
      end
      DEBUG_TAKEN: begin

        // Indicate that debug is taken
        ctrl_fsm_o.dbg_ack = 1'b1;

        // Clear flags for halting IF during single step
        single_step_halt_if_n = 1'b0;

        // Set pc
        ctrl_fsm_o.pc_set = 1'b1;
        ctrl_fsm_o.pc_mux = PC_TRAP_DBD;

        // Save CSRs
        ctrl_fsm_o.csr_save_cause = !(ebreak_in_wb && debug_mode_q);  // No CSR update for ebreak in debug mode
        ctrl_fsm_o.debug_csr_save = 1'b1;

        // debug_cause_q set when decision was made to enter debug
        if (debug_cause_q != DBG_CAUSE_STEP) begin
          // Kill pipeline
          ctrl_fsm_o.kill_if = 1'b1;
          ctrl_fsm_o.kill_id = 1'b1;
          ctrl_fsm_o.kill_ex = 1'b1;
          // Ebreak that causes debug entry should not be killed, otherwise RVFI will skip it
          // Trigger match should also be signalled as not killed (all write enables are suppressed in ID), otherwise RVFI/ISS will not attempt to execute and detect trigger
          // Ebreak during debug_mode restarts from dm_halt_addr, without CSR updates. Not killing ebreak due to the same RVFI/ISS reasons.
          // Neither ebreak nor trigger match have any state updates in WB. For trigger match, all write enables are suppressed in the ID stage.
          //   Thus this change is not visible to core state, only for RVFI use.
          // todo: Move some logic to RVFI instead?
          ctrl_fsm_o.kill_wb = !((debug_cause_q == DBG_CAUSE_EBREAK) || (debug_cause_q == DBG_CAUSE_TRIGGER) ||
                                (debug_mode_q && ebreak_in_wb));

          // Save pc from oldest valid instruction
          if (ex_wb_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_WB;
          end else if (id_ex_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_EX;
          end else if (if_id_pipe_i.instr_valid) begin
            pipe_pc_mux_ctrl = PC_ID;
          end else begin
            pipe_pc_mux_ctrl = PC_IF;
          end
        end else begin
          // Single step
          // Only kill IF. WB should be allowed to complete
          // ID and EX are empty as IF is blocked after one issue in single step mode
          ctrl_fsm_o.kill_if = 1'b1;
          ctrl_fsm_o.kill_id = 1'b0;
          ctrl_fsm_o.kill_ex = 1'b0;
          ctrl_fsm_o.kill_wb = 1'b0;

          // Should use pc from IF (next insn, as IF is halted after first issue)
          pipe_pc_mux_ctrl = PC_IF;
        end

        // Enter debug mode next cycle
        debug_mode_n = 1'b1;
        ctrl_fsm_ns = FUNCTIONAL;
      end
      // State for CLIC vectoring (and Zc table jumps)
      // In this state a fetch has been ordered, and the controller
      // is waiting for the pointer to arrive in the decode stage.
      POINTER_FETCH: begin
        if (if_id_pipe_i.instr_meta.clic_ptr && if_id_pipe_i.instr_valid) begin
          // Function pointer reached ID stage, do another jump
          // if no faults happened during pointer fetch. (mcause.minhv will stay high for faults)
          // todo: deal with integrity related faults for E40S.
          if(!((if_id_pipe_i.instr.mpu_status != MPU_OK) || if_id_pipe_i.instr.bus_resp.err)) begin
            ctrl_fsm_o.pc_set = 1'b1;
            ctrl_fsm_o.pc_mux = PC_POINTER;
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.csr_clear_minhv = 1'b1;

            // Jump to debug taken in case of a pending single step.
            // We should enter debug without executing any instruction, and let dpc
            // point to the first instruction in the handler
            ctrl_fsm_ns = pending_single_step_ptr ? DEBUG_TAKEN : FUNCTIONAL;
          end else begin
            // If the pointer fetch faulted, we don't jump to the target and return to FUNCTIONAL.
            // Any pending single step will not be taken (the irq handler instruction fetch faulted),
            // and the associated exception or NMI will be taken in FUNCTIONAL along with the single step once
            // the pointer reaches WB. Dpc will then point to the first instruction in the exception/NMI handler.
            ctrl_fsm_ns = FUNCTIONAL;
          end
          // Note: If the pointer fetch faulted (pma/pmp/bus error), an exception or NMI will
          // be taken once the pointer fetch reachces WB (two cycles after the current)
          // The FSM must be in the FUNCTIONAL state to take the exception or NMI.
          // A faulted pointer (in ID) should not cause debug entry either,
        end
      end
      default: begin
        // should never happen
        ctrl_fsm_o.instr_req = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase

    // Detect first insn issue in single step after dret
    // Used to block further issuing
    if (!ctrl_fsm_o.debug_mode && dcsr_i.step && !single_step_halt_if_q && (if_valid_i && id_ready_i)) begin
      single_step_halt_if_n = 1'b1;
    end

    // Clear jump/branch flag when new insn is emitted from IF
    if (branch_taken_q && if_valid_i && id_ready_i) begin
      branch_taken_n = 1'b0;
    end
  end

  // Wakeup from sleep
  assign ctrl_fsm_o.wake_from_sleep    = irq_wu_ctrl_i || pending_debug || debug_mode_q;
  assign ctrl_fsm_o.debug_wfi_no_sleep = debug_mode_q || dcsr_i.step || trigger_match_in_wb;

  ////////////////////
  // Flops          //
  ////////////////////

  // FSM state and debug_mode
  always_ff @(posedge clk , negedge rst_n) begin
    if (rst_n == 1'b0) begin
      ctrl_fsm_cs <= RESET;
      debug_mode_q <= 1'b0;
      debug_cause_q <= DBG_CAUSE_NONE;
    end else begin
      ctrl_fsm_cs   <= ctrl_fsm_ns;
      debug_mode_q  <= debug_mode_n;
      debug_cause_q <= debug_cause_n;
    end
  end

  // debug_mode_if is a control input for the if stage.
  // For both debug mode entry end exit, the IF, ID and EX stages are killed. While the IF stage is killed it starts
  // fetching the next instruction (sets the obi request high), requiring a valid debug mode signal for this fetch.
  // The debug_mode_if signal is valid for all IF fetches.
  assign ctrl_fsm_o.debug_mode_if = debug_mode_n;
  assign ctrl_fsm_o.debug_mode    = debug_mode_q;

  // sticky version of debug_req (must be on clk_ungated_i such that incoming pulse before core is enabled is not missed)
  always_ff @(posedge clk_ungated_i, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      debug_req_q <= 1'b0;
    end else begin
      if (debug_req_i) begin
        debug_req_q <= 1'b1;
      end else if (debug_mode_q) begin
        debug_req_q <= 1'b0;
      end
    end
  end

  // Sticky version of lsu_err_wb_i
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      nmi_pending_q <= 1'b0;
      nmi_is_store_q <= 1'b0;
    end else begin
      if (lsu_err_wb_i[0] && !nmi_pending_q) begin
        // Set whenever an error occurs in WB for the LSU, unless we already have an NMI pending.
        // Later errors could overwrite the bit for load/store type, and with mtval the address would be overwritten.
        // todo: if mtval is implemented, address must be sticky as well
        nmi_pending_q <= 1'b1;
        nmi_is_store_q <= lsu_err_wb_i[1];
      // Clear when the controller takes the NMI
      end else if (ctrl_fsm_o.pc_set && (ctrl_fsm_o.pc_mux == PC_TRAP_NMI)) begin
        nmi_pending_q <= 1'b0;
      end
    end
  end

  // Flop used to gate if_valid after one instruction issued
  // in single step mode
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      single_step_halt_if_q <= 1'b0;
      branch_taken_q        <= 1'b0;
    end else begin
      single_step_halt_if_q <= single_step_halt_if_n;
      branch_taken_q        <= branch_taken_n;
    end
  end

  // Flops for fencei handshake request
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      fencei_flush_req_o   <= 1'b0;
      fencei_req_and_ack_q <= 1'b0;
    end else begin

      // Flop fencei_flush_ack_i to break timing paths
      // fencei_flush_ack_i must be qualified with fencei_flush_req_o
      fencei_req_and_ack_q <= fencei_flush_req_o && fencei_flush_ack_i;

      // Set fencei_flush_req_o based on FSM output. Clear upon req&&ack.
      if (fencei_flush_req_o && fencei_flush_ack_i) begin
        fencei_flush_req_o <= 1'b0;
      end
      else if (fencei_flush_req_set) begin
        fencei_flush_req_o <= 1'b1;
      end
    end
  end

  // minstret event
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      wb_counter_event <= 1'b0;
    end else begin
      // When the last part of an instruction reaches WB we may increment counters,
      // unless WB stage is halted. A halted instruction in WB may or may not be killed later,
      // thus we cannot count it until we know for sure if it will retire.
      // i.e halt_wb due to debug will result in killed WB, while for fence.i it will retire.
      // Note that this event bit is further gated before sent to the actual counters in case
      // other conditions prevent counting.
      // CLIC: Exluding pointer fetches as they are not instructions
      if (ex_valid_i && wb_ready_i && last_op_ex_i && !ex_wb_pipe_i.instr_meta.clic_ptr) begin
        wb_counter_event <= 1'b1;
      end else begin
        // Keep event flag high while WB is halted, as we don't know if it will retire yet
        if (!ctrl_fsm_o.halt_wb) begin
          wb_counter_event <= 1'b0;
        end
      end
    end
  end


  /////////////////////
  // Debug state FSM //
  /////////////////////
  always_ff @(posedge clk , negedge rst_n) begin
    if (rst_n == 1'b0) begin
      debug_fsm_cs <= HAVERESET;
    end else begin
      debug_fsm_cs <= debug_fsm_ns;
    end
  end

  always_comb begin
    debug_fsm_ns = debug_fsm_cs;

    case (debug_fsm_cs)
      HAVERESET: begin
        if (debug_mode_n || (ctrl_fsm_ns == BOOT_SET)) begin
          if (debug_mode_n) begin
            debug_fsm_ns = HALTED;
          end else begin
            debug_fsm_ns = RUNNING;
          end
        end
      end

      RUNNING: begin
        if (debug_mode_n) begin
          debug_fsm_ns = HALTED;
        end
      end

      HALTED: begin
        if (!debug_mode_n) begin
          debug_fsm_ns = RUNNING;
        end
      end

      default: begin
        debug_fsm_ns = HAVERESET;
      end
    endcase
  end

  assign ctrl_fsm_o.debug_havereset = debug_fsm_cs[HAVERESET_INDEX];
  assign ctrl_fsm_o.debug_running   = debug_fsm_cs[RUNNING_INDEX];
  assign ctrl_fsm_o.debug_halted    = debug_fsm_cs[HALTED_INDEX];


  //---------------------------------------------------------------------------
  // eXtension interface
  //---------------------------------------------------------------------------

  generate
    if (X_EXT) begin : x_ext
      logic commit_valid_q; // Sticky bit for commit_valid
      logic commit_kill_q;  // Sticky bit for commit_kill
      logic kill_rejected;  // Signal used to kill rejected xif instructions

      // TODO: Add assertion to check the following:
      // Every issue interface transaction (whether accepted or not) has an associated commit interface
      // transaction and both interfaces use a matching transaction ordering.

      // Commit an offloaded instruction in the first cycle where EX is not halted, or EX is killed.
      //       Only commit when there is an offloaded instruction in EX (accepted or not), and we have not
      //       previously signalled commit for the same instruction. Rejected xif instructions gets killed
      //       with commit_kill=1 (pipeline is not killed as we need to handle the illegal instruction in WB)
      // Can only allow commit when older instructions are guaranteed to complete without exceptions
      //       - EX is halted if offloaded in WB can cause an exception, causing below to evaluate to 0.
      assign xif_commit_if.commit_valid       = (!ctrl_fsm_o.halt_ex || ctrl_fsm_o.kill_ex) &&
                                                 (id_ex_pipe_i.xif_en && id_ex_pipe_i.instr_valid) &&
                                                 !commit_valid_q; // Make sure we signal only once per instruction

      assign xif_commit_if.commit.id          = id_ex_pipe_i.xif_meta.id;
      assign xif_commit_if.commit.commit_kill = xif_csr_error_i || ctrl_fsm_o.kill_ex || kill_rejected;

      // Signal commit_kill=1 to all instructions rejected by the eXtension interface
      assign kill_rejected = (id_ex_pipe_i.xif_en && !id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.instr_valid;

      // Signal (to EX stage), that an (attempted) offloaded instructions is killed (clears ex_wb_pipe.xif_en)
      assign ctrl_fsm_o.kill_xif = xif_commit_if.commit.commit_kill || commit_kill_q;

      // Flag used to make sure we only signal commit_valid once for each instruction
      always_ff @(posedge clk, negedge rst_n) begin : commit_valid_ctrl
        if (rst_n == 1'b0) begin
          commit_valid_q <= 1'b0;
          commit_kill_q  <= 1'b0;
        end else begin
          if ((ex_valid_i && wb_ready_i) || ctrl_fsm_o.kill_ex) begin
            commit_valid_q <= 1'b0;
            commit_kill_q  <= 1'b0;
          end else begin
            commit_valid_q <= (xif_commit_if.commit_valid || commit_valid_q);
            commit_kill_q  <= (xif_commit_if.commit.commit_kill || commit_kill_q);
          end
        end
      end

    end else begin : no_x_ext

      assign xif_commit_if.commit_valid       = '0;
      assign xif_commit_if.commit.id          = '0;
      assign xif_commit_if.commit.commit_kill = '0;
      assign ctrl_fsm_o.kill_xif              = 1'b0;

    end
  endgenerate

endmodule
