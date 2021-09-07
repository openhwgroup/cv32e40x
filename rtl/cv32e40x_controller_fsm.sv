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
(
  // Clocks and reset
  input  logic        clk,                        // Gated clock
  input  logic        clk_ungated_i,              // Ungated clock
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start executing

  // From bypass logic
  input  ctrl_byp_t   ctrl_byp_i,

  // From ID stage
  input  if_id_pipe_t if_id_pipe_i,
  input  logic        mret_id_i,                  // mret in ID stage
  input  logic        dret_id_i,                  // dret in ID stage
  input  logic [1:0]  ctrl_transfer_insn_i,       // jump is being calculated in ALU
  input  logic [1:0]  ctrl_transfer_insn_raw_i,   // jump is being calculated in ALU

  // From WB stage
  input  ex_wb_pipe_t ex_wb_pipe_i,

  // From EX stage
  input  id_ex_pipe_t id_ex_pipe_i,        
  input  logic        branch_decision_ex_i,       // branch decision signal from EX ALU
  input  logic        obi_data_req_i,             // LSU OBI interface req

  // From WB stage
  input  logic        lsu_err_wb_i,               // LSU caused bus_error in WB stage
  input  logic [31:0] lsu_addr_wb_i,              // LSU address in WB stage

  // From LSU (WB)
  input  mpu_status_e lsu_mpu_status_wb_i,        // MPU status (WB timing)

  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,             // irq requst
  input  logic [4:0]  irq_id_ctrl_i,              // irq id
  input  logic        irq_wu_ctrl_i,              // irq wakeup control
  input  PrivLvl_t    current_priv_lvl_i,         // Current running priviledge level

  // From cs_registers
  input logic  [1:0]  mtvec_mode_i,           
  input  logic        debug_single_step_i,        // dcsr.step from cs_registers
  input  logic        debug_ebreakm_i,            // dcsr.ebreakm from cs_registers
  input  logic        debug_trigger_match_id_i,   // Trigger match from cs_registers

  // Toplevel input
  input  logic        debug_req_i,                // External debug request

  // All controller FSM outputs
  output ctrl_fsm_t   ctrl_fsm_o,

  // Stage valid/ready signals
  input  logic        if_valid_i,       // IF stage has valid (non-bubble) data for next stage
  input  logic        id_ready_i,       // ID stage is ready for new data
  input  logic        ex_valid_i,       // EX stage has valid (non-bubble) data for next stage
  input  logic        wb_ready_i,       // WB stage is ready for new data,
  input  logic        wb_valid_i,       // WB stage ha valid (non-bubble) data

  // Fencei flush handshake
  output logic        fencei_flush_req_o,
  input logic         fencei_flush_ack_i
);

   // FSM state encoding
  ctrl_state_e ctrl_fsm_cs, ctrl_fsm_ns;

  // Debug state
  debug_state_e debug_fsm_cs, debug_fsm_ns;

  // Sticky version of debug_req_i
  logic debug_req_q;

  // Debug mode
  logic debug_mode_n;
  logic debug_mode_q;

  // Signals used for halting IF after first instruction
  // during single step
  logic single_step_halt_if_n;
  logic single_step_halt_if_q; // Halting IF after issuing one insn in single step mode

  
  // Events in ID
  logic jump_in_id;
  logic jump_taken_id;

  // Events in EX
  logic branch_in_ex;
  logic branch_taken_ex;

  logic branch_taken_n;
  logic branch_taken_q;
  
  // Events in WB
  logic exception_in_wb;
  logic [5:0] exception_cause_wb;
  logic wfi_in_wb;
  logic fencei_in_wb;
  logic mret_in_wb;
  logic dret_in_wb;
  logic ebreak_in_wb;
  logic trigger_match_in_wb;
  logic pending_nmi;
  logic pending_debug;
  logic pending_single_step;
  logic pending_interrupt;

  // Flags for allowing interrupt and debug
  // TODO:OK:low Add flag for exception_allowed
  logic interrupt_allowed;
  logic debug_allowed;
  logic single_step_allowed;

  // Flops for debug cause
  logic [2:0] debug_cause_n;
  logic [2:0] debug_cause_q;
  
// Data request has been clocked without insn moving to WB
  logic obi_data_req_q; // todo: should really look at 'trans'; rename accordingly

  logic [4:0] exc_cause; // id of taken interrupt

  logic       fencei_ready;
  logic       fencei_req_and_ack_q;

  assign fencei_ready = 1'b1; // TODO: connect when write buffer is implemented
      
  // Mux selector for vectored IRQ PC
  assign ctrl_fsm_o.m_exc_vec_pc_mux = (mtvec_mode_i == 2'b0) ? 5'h0 : exc_cause;
  
  ////////////////////////////////////////////////////////////////////


  // ID stage
  // A jump is taken in ID for jump instructions, and also for mret instructions
  // Checking validity of jump instruction or mret with if_id_pipe_i.instr_valid.
  // Using the ID stage local instr_valid would bring halt_id and kill_id into the equation
  // causing a path from data_rvalid to instr_addr_o/instr_req_o/instr_memtype_o via the jumps pc_set=1
  assign jump_in_id = ((((ctrl_transfer_insn_raw_i == BRANCH_JALR) || (ctrl_transfer_insn_raw_i == BRANCH_JAL)) && !ctrl_byp_i.jr_stall) ||
                         (mret_id_i && !ctrl_byp_i.csr_stall)) &&
                         if_id_pipe_i.instr_valid;

  // Blocking on branch_taken_q, as a jump has already been taken
  assign jump_taken_id = jump_in_id && !branch_taken_q; // todo: RVFI does not use jump_taken_id (which is not in itself an issue); we should have an assertion showing that the target address remains constant during jump_in_id; same remark for branches

  // EX stage 
  // Branch taken for valid branch instructions in EX with valid decision
  
  assign branch_in_ex = id_ex_pipe_i.branch_in_ex && id_ex_pipe_i.instr_valid && branch_decision_ex_i;

  // Blocking on branch_taken_q, as a branch ha already been taken
  assign branch_taken_ex = branch_in_ex && !branch_taken_q;

  // TODO:OK:low Add missing exception types when implemented
  // Exception in WB if the following evaluates to 1
  assign exception_in_wb = ((ex_wb_pipe_i.instr.mpu_status != MPU_OK) ||
                            ex_wb_pipe_i.instr.bus_resp.err           ||
                            ex_wb_pipe_i.illegal_insn                 ||
                            ex_wb_pipe_i.ecall_insn                   ||
                            ex_wb_pipe_i.ebrk_insn                    ||
                            (lsu_mpu_status_wb_i != MPU_OK))          && ex_wb_pipe_i.instr_valid;

  // Set exception cause
  assign exception_cause_wb = ex_wb_pipe_i.instr.mpu_status != MPU_OK       ? EXC_CAUSE_INSTR_FAULT     :
                              ex_wb_pipe_i.instr.bus_resp.err               ? EXC_CAUSE_INSTR_BUS_FAULT :
                              ex_wb_pipe_i.illegal_insn                     ? EXC_CAUSE_ILLEGAL_INSN    :
                              ex_wb_pipe_i.ecall_insn                       ? EXC_CAUSE_ECALL_MMODE     :
                              ex_wb_pipe_i.ebrk_insn                        ? EXC_CAUSE_BREAKPOINT      :
                              (lsu_mpu_status_wb_i == MPU_WR_FAULT)         ? EXC_CAUSE_STORE_FAULT     :
                              (lsu_mpu_status_wb_i == MPU_RE_FAULT)         ? EXC_CAUSE_LOAD_FAULT      :
                              6'h0; // todo:ok: could default to EXC_CAUSE_LOAD_FAULT instead

  // wfi in wb
  assign wfi_in_wb = ex_wb_pipe_i.wfi_insn && ex_wb_pipe_i.instr_valid;

  // fencei in wb
  assign fencei_in_wb = ex_wb_pipe_i.fencei_insn && ex_wb_pipe_i.instr_valid;

  // mret in wb
  assign mret_in_wb = ex_wb_pipe_i.mret_insn && ex_wb_pipe_i.instr_valid;

  // dret in wb
  assign dret_in_wb = ex_wb_pipe_i.dret_insn && ex_wb_pipe_i.instr_valid;

  // ebreak in wb
  assign ebreak_in_wb = ex_wb_pipe_i.ebrk_insn && ex_wb_pipe_i.instr_valid;

  // Trigger match in wb
  // Trigger_match during debug mode is masked in the trigger logic inside cs_registers.sv
  assign trigger_match_in_wb = (ex_wb_pipe_i.trigger_match && ex_wb_pipe_i.instr_valid);

  // Pending NMI
  assign pending_nmi = 1'b0;

  // Debug //

  // Single step will need to finish insn in WB, including LSU
  // LSU will now set valid_1_o only for second part of misaligned instructions.
  // We can always allow single step when checking for wb_valid_i in 'pending_single_step'
  // - no other instructions should be in the pipeline.
  assign single_step_allowed = 1'b1;
                             
  // Single step are mutually exclusive from any other reason to enter debug
  assign pending_single_step = (!debug_mode_q && debug_single_step_i && wb_valid_i) && !pending_debug;

  // Regular debug will kill insn in WB, do not allow for LSU in WB as insn must finish with rvalid
  // or for any case where a LSU in EX has asserted its obi data_req for at least one cycle.
  // For misaligned LSU, if the first phase just arrived in EX, we may kill it and enter debug.
  //  - If first phase stays in EX for more than one cycle, obi_data_req_q will be 1 and block debug.
  //  - When first phase arrives in WB, we block debug. If first phase in WB finishes with rvalid
  //    before second phase in EX gets grant, we block on obi_data_req_q
  assign debug_allowed = !(ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid) && !obi_data_req_q;

  // Debug pending for any other reason than single step
  assign pending_debug = (trigger_match_in_wb) ||
                         ((debug_req_i || debug_req_q) && !debug_mode_q) ||    // External request
                         (ebreak_in_wb && debug_ebreakm_i && !debug_mode_q) || // Ebreak with dcsr.ebreakm==1
                         (ebreak_in_wb && debug_mode_q); // Ebreak during debug_mode restarts execution from dm_halt_addr, as a regular debug entry without CSR updates.

  // Determine cause of debug
  // pending_single_step may only happen if no other causes for debug are true.
  // The flopped version of this is checked during DEBUG_TAKEN state (one cycle delay)
  assign debug_cause_n = pending_single_step ? DBG_CAUSE_STEP :
                         trigger_match_in_wb ? DBG_CAUSE_TRIGGER :
                         (ebreak_in_wb && debug_ebreakm_i && !debug_mode_q) ? DBG_CAUSE_EBREAK :
                         DBG_CAUSE_HALTREQ;

  // Debug cause to CSR from flopped version (valid during DEBUG_TAKEN)
  assign ctrl_fsm_o.debug_cause = debug_cause_q;

  
  assign pending_interrupt = irq_req_ctrl_i && !debug_mode_q; // todo: explain why !debug_mode_q is used here (it does not seem logical to use that to qualify pending interrupts)

  // Allow interrupts to be taken only if there is no data request in WB, 
  // and no data_req has been clocked from EX to environment.
  // LSU instructions which were suppressed due to previous exceptions or trigger match
  // will be interruptable as they were convered to NOP in ID stage.
  // TODO:OK:low May allow interuption of Zce to idempotent memories
  assign interrupt_allowed = !(ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid) && !obi_data_req_q && !debug_mode_q;
                               
  // Performance counter events
  assign ctrl_fsm_o.mhpmevent.minstret = wb_valid_i && !exception_in_wb && !trigger_match_in_wb;
  assign ctrl_fsm_o.mhpmevent.load = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.store = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.jump = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.branch = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.branch_taken = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.compressed = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.jr_stall = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.imiss = 1'b0; // todo:low
  assign ctrl_fsm_o.mhpmevent.ld_stall = 1'b0; // todo:low

/* todo:low Below are the original events definitions; check which ones to keep. If needed the actual definition can be changed (there is no backward compatibility requirement).
  // Performance Counter Events
  //TODO:OK: Fix counters to reflect new controller behaviour
  // Illegal/ebreak/ecall are never counted as retired instructions. Note that actually issued instructions
  // are being counted; the manner in which CSR instructions access the performance counters guarantees
  // that this count will correspond to the retired isntructions count.
  assign minstret = id_valid && is_last && !(illegal_insn || ebrk_insn || ecall_insn);

  always_ff @(posedge clk , negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      id_valid_q                 <= 1'b0;
      mhpmevent_minstret_o       <= 1'b0;
      mhpmevent_load_o           <= 1'b0;
      mhpmevent_store_o          <= 1'b0;
      mhpmevent_jump_o           <= 1'b0;
      mhpmevent_branch_o         <= 1'b0;
      mhpmevent_compressed_o     <= 1'b0;
      mhpmevent_branch_taken_o   <= 1'b0;
      mhpmevent_jr_stall_o       <= 1'b0;
      mhpmevent_imiss_o          <= 1'b0;
      mhpmevent_ld_stall_o       <= 1'b0;
    end
    else
    begin
      // Helper signal, id_valid may be 1'b1 to update EX for misaligned LSU, gate off to not count events in those cases
      id_valid_q                 <= id_valid && is_last;
      // ID stage counts
      mhpmevent_minstret_o       <= minstret;
      mhpmevent_load_o           <= minstret && lsu_en && !lsu_we;
      mhpmevent_store_o          <= minstret && lsu_en && lsu_we;
      mhpmevent_jump_o           <= minstret && ((ctrl_transfer_insn_o == BRANCH_JAL) || (ctrl_transfer_insn_o == BRANCH_JALR));
      mhpmevent_branch_o         <= minstret && (ctrl_transfer_insn_o == BRANCH_COND);
      mhpmevent_compressed_o     <= minstret && if_id_pipe_i.is_compressed;
      // EX stage count
      mhpmevent_branch_taken_o   <= mhpmevent_branch_o && branch_decision_i;
      // IF stage count
      mhpmevent_imiss_o          <= perf_imiss_i;
      // Jump-register-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_jr_stall_o       <= ctrl_byp_i.jr_stall && !ctrl_fsm_i.halt_id && id_valid_q;
      // Load-use-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_ld_stall_o       <= ctrl_byp_i.load_stall && !ctrl_fsm_i.halt_id && id_valid_q;
    end
  end
*/

  //////////////
  // FSM comb //
  //////////////
  always_comb begin
    // Default values
    ctrl_fsm_ns = ctrl_fsm_cs;
    ctrl_fsm_o.ctrl_busy = 1'b1;
    ctrl_fsm_o.instr_req = 1'b1;

    ctrl_fsm_o.pc_mux    = PC_BOOT;
    ctrl_fsm_o.pc_set = 1'b0;

    ctrl_fsm_o.irq_ack = 1'b0;
    ctrl_fsm_o.irq_id  = '0;

    // IF stage is halted if an instruction has been issued during single step
    // to avoid more than one instructions passing down the pipe.
    ctrl_fsm_o.halt_if = single_step_halt_if_q;
    // ID stage is halted for regular stalls (i.e. stalls for which the instruction
    // currently in ID is not ready to be issued yet). Also halted if interrupt or debug pending
    // but not allowed to be taken. This is to create an interruptible bubble in WB.
    ctrl_fsm_o.halt_id = ctrl_byp_i.jr_stall || ctrl_byp_i.load_stall || ctrl_byp_i.csr_stall || ctrl_byp_i.wfi_stall ||
                         (pending_interrupt && !interrupt_allowed) ||
                         (pending_debug && !debug_allowed);
    // Halting EX if minstret_stall occurs. Otherwise we would read the wrong minstret value
    ctrl_fsm_o.halt_ex = ctrl_byp_i.minstret_stall;
    ctrl_fsm_o.halt_wb = 1'b0;

    // By default no stages are killed
    ctrl_fsm_o.kill_if = 1'b0;
    ctrl_fsm_o.kill_id = 1'b0;
    ctrl_fsm_o.kill_ex = 1'b0;
    ctrl_fsm_o.kill_wb = 1'b0;

    ctrl_fsm_o.csr_restore_mret    = 1'b0;
    ctrl_fsm_o.csr_restore_dret    = 1'b0;
    ctrl_fsm_o.csr_save_if         = 1'b0; // todo: can we send the correct pc to the CSR module instead of the separate save_* signals? (Keep the save signals local to this file, but move the pc mux from CSR to here)
    ctrl_fsm_o.csr_save_id         = 1'b0;
    ctrl_fsm_o.csr_save_ex         = 1'b0;
    ctrl_fsm_o.csr_save_wb         = 1'b0;
    ctrl_fsm_o.csr_save_cause      = 1'b0;
    ctrl_fsm_o.csr_cause           = 32'h0;

    ctrl_fsm_o.exc_pc_mux          = EXC_PC_IRQ;
    exc_cause                      = 5'b0;

    debug_mode_n                   = debug_mode_q;
    ctrl_fsm_o.debug_csr_save      = 1'b0;
    ctrl_fsm_o.block_data_addr     = 1'b0;
    
    // Single step halting of IF
    single_step_halt_if_n = single_step_halt_if_q;

    // Ensure jumps and branches are taken only once
    branch_taken_n                 = branch_taken_q;

    // fencei external handshake request
    fencei_flush_req_o             = 1'b0;

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
        // NMI // TODO:OK:low Implement
        if (pending_nmi) begin
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

          ctrl_fsm_o.pc_set     = 1'b1;
          ctrl_fsm_o.pc_mux     = PC_EXCEPTION;
          ctrl_fsm_o.exc_pc_mux = EXC_PC_IRQ;
          exc_cause  = irq_id_ctrl_i;

          ctrl_fsm_o.irq_ack = 1'b1;
          ctrl_fsm_o.irq_id  = irq_id_ctrl_i;

          ctrl_fsm_o.csr_save_cause  = 1'b1;
          ctrl_fsm_o.csr_cause.interrupt = 1'b1;
          ctrl_fsm_o.csr_cause.exception_code = {1'b0, irq_id_ctrl_i};

          // Save pc from oldest valid instruction
          if (ex_wb_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_wb = 1'b1;
          end else if (id_ex_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_ex = 1'b1;
          end else if (if_id_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_id = 1'b1;
          end else begin
            // IF PC will always be valid as it points to the next
            // instruction to be issued from IF to ID.
            ctrl_fsm_o.csr_save_if = 1'b1;
          end

          // Unstall IF in case of single stepping
          if (debug_single_step_i) begin
            single_step_halt_if_n = 1'b0;
          end
        end else begin
          if (exception_in_wb) begin
            // TODO:OK:low Must check if we are allowed to take exceptions
            //          Applies to PMA on misaligned
            // Kill all stages
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            ctrl_fsm_o.kill_wb = 1'b0; // All write enables are suppressed, no need to kill WB.

            // Set pc to exception handler
            ctrl_fsm_o.pc_set       = 1'b1;
            ctrl_fsm_o.pc_mux       = PC_EXCEPTION;
            ctrl_fsm_o.exc_pc_mux   = debug_mode_q ? EXC_PC_DBE : EXC_PC_EXCEPTION;

            // Save CSR from WB
            ctrl_fsm_o.csr_save_wb     = 1'b1;
            ctrl_fsm_o.csr_save_cause  = !debug_mode_q; // Do not update CSRs if in debug mode
            ctrl_fsm_o.csr_cause.exception_code = exception_cause_wb;
          // Special insn
          end else if (wfi_in_wb) begin
            // Not halting EX/WB to allow insn (interruptible bubble) in EX to pass to WB before sleeping
            ctrl_fsm_o.halt_if = 1'b1;
            ctrl_fsm_o.halt_id = 1'b1;
            ctrl_fsm_o.instr_req = 1'b0;
            ctrl_fsm_ns = SLEEP;
          end else if (fencei_in_wb) begin

            // Kill if,id and ex stages, halt wb stage
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            ctrl_fsm_o.halt_wb = 1'b1;

            if(fencei_ready) begin
              // Core is ready to initiate external fencei handshake
              ctrl_fsm_ns = FENCEI_HANDSHAKE;
            end
          end else if (dret_in_wb) begin
            // Dret takes jump from WB stage
            // Kill previous stages and jump to pc in dpc
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            
            ctrl_fsm_o.pc_mux  = PC_DRET;
            ctrl_fsm_o.pc_set  = 1'b1;

            ctrl_fsm_o.csr_restore_dret  = 1'b1;

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
            // kill_if
            ctrl_fsm_o.kill_if = 1'b1;

            // Jumps in ID (JAL, JALR, mret, uret, dret)
            if (mret_id_i) begin
              ctrl_fsm_o.pc_mux     = debug_mode_q ? PC_EXCEPTION : PC_MRET;
              ctrl_fsm_o.pc_set     = 1'b1;
              ctrl_fsm_o.exc_pc_mux = EXC_PC_DBE; // Only used in debug mode
            end else begin
              ctrl_fsm_o.pc_mux = PC_JUMP;
              ctrl_fsm_o.pc_set = 1'b1;
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
      end // case: FUNCTIONAL
      FENCEI_HANDSHAKE: begin

        // Set external handshake request
        fencei_flush_req_o = 1'b1;
        
        // Stall the pipeline until the handshake is complete
        ctrl_fsm_o.kill_if = 1'b1; // TODO: this should not be needed. IF is already killed and halt_wb should give backpressure
        ctrl_fsm_o.halt_wb = 1'b1;
        
        if(fencei_req_and_ack_q) begin
          // fencei req and ack were set in the same cycle, unhalt wb and jump to wb.pc + 4
          ctrl_fsm_o.pc_set  = 1'b1;
          ctrl_fsm_o.pc_mux  = PC_FENCEI;
          ctrl_fsm_o.halt_wb = 1'b0;
          ctrl_fsm_ns        = FUNCTIONAL;

          // Clear fencei_flush_req_o
          fencei_flush_req_o = 1'b0;
        end
      end
      SLEEP: begin
        ctrl_fsm_o.ctrl_busy = 1'b0;
        ctrl_fsm_o.instr_req = 1'b0;

        ctrl_fsm_o.halt_wb   = 1'b1; // implicitly halts earlier stages
        if(ctrl_fsm_o.wake_from_sleep) begin
          ctrl_fsm_ns = FUNCTIONAL;
          ctrl_fsm_o.ctrl_busy = 1'b1;
        end
      end
      DEBUG_TAKEN: begin
        // Clear flags for halting IF during single step
        single_step_halt_if_n = 1'b0;

        // Set pc
        ctrl_fsm_o.pc_set     = 1'b1;
        ctrl_fsm_o.pc_mux     = PC_EXCEPTION;
        ctrl_fsm_o.exc_pc_mux = EXC_PC_DBD;

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
            ctrl_fsm_o.csr_save_wb = 1'b1;
          end else if (id_ex_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_ex = 1'b1;
          end else if (if_id_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_id = 1'b1;
          end else begin
            ctrl_fsm_o.csr_save_if = 1'b1;
          end
        end else begin
          // Single step
          // Only kill IF. WB should be allowed to complete
          // ID and EX are empty as IF is blocked after one issue in single step mode
          ctrl_fsm_o.kill_if = 1'b1;
          ctrl_fsm_o.kill_id = 1'b0;
          ctrl_fsm_o.kill_ex = 1'b0;
          ctrl_fsm_o.kill_wb = 1'b0;

          // Should use pc from IF (next insn, as if is halted after first issue)
          // Exception for single step + ebreak, as addr of ebreak (in WB) shall be stored
             // or trigger match, as timing=0 permits us from executing triggered insn before 
             // entering debug mode
          if((ebreak_in_wb && debug_ebreakm_i) || trigger_match_in_wb) begin
            ctrl_fsm_o.csr_save_wb = 1'b1;
          end else begin
            ctrl_fsm_o.csr_save_if = 1'b1;
          end
        end

        // Enter debug mode next cycle
        debug_mode_n = 1'b1;
        ctrl_fsm_ns = FUNCTIONAL;
      end
      default: begin
        // should never happen
        ctrl_fsm_o.instr_req = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase

    // Detect first insn issue in single step after dret
    // Used to block further issuing
    if(!ctrl_fsm_o.debug_mode && debug_single_step_i && !single_step_halt_if_q && (if_valid_i && id_ready_i)) begin
      single_step_halt_if_n = 1'b1;
    end

    // Clear jump/branch flag when new insn is emitted from IF
    if(branch_taken_q && if_valid_i && id_ready_i) begin
      branch_taken_n = 1'b0;
    end
  end

  // Wakeup from sleep
  assign ctrl_fsm_o.wake_from_sleep    = irq_wu_ctrl_i || pending_debug || debug_mode_q;
  assign ctrl_fsm_o.debug_wfi_no_sleep = debug_mode_q || debug_single_step_i || trigger_match_in_wb;

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

  assign ctrl_fsm_o.debug_mode = debug_mode_q;

  // Detect when data_req has been clocked, and lsu insn is still in EX
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      obi_data_req_q <= 1'b0;
    end else begin
      if (obi_data_req_i && !(ex_valid_i && wb_ready_i)) begin
        obi_data_req_q <= 1'b1;
      end else if (ex_valid_i && wb_ready_i) begin
        obi_data_req_q <= 1'b0;
      end
    end
  end

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

  // Flop fencei_flush_ack_i to break timing paths
  // Qualify with fencei_flush_req_o, since fencei_flush_ack_i is only valid when fencei_flush_req_o is set
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      fencei_req_and_ack_q <= 1'b0;
    end else begin
      fencei_req_and_ack_q <= fencei_flush_req_o && fencei_flush_ack_i;
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

endmodule //cv32e40x_controller_fsm
