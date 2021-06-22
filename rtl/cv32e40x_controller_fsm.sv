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
  input  logic        jr_stall_i,                 // There is a jr-stall pending  

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
  input  logic        data_req_i,                 // Data interface trans_valid // TODO: pick better name; is this the OBI signal or the signal before the MPU?

  // From WB stage
  input  logic        lsu_err_wb_i,               // LSU caused bus_error in WB stage
  input  logic [31:0] lsu_addr_wb_i,              // LSU address in WB stage
  input  logic        lsu_en_wb_i,                // LSU data is written back in WB

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
  output ctrl_fsm_t    ctrl_fsm_o,

  // From IF stage
  input  logic        if_valid_i,       // IF stage has valid (non-bubble) data for next stage
  input  logic        if_ready_i,       // IF stage is ready for new data
  input  logic        id_ready_i,       // ID stage is ready for new data
  input  logic        ex_valid_i,       // EX stage has valid (non-bubble) data for next stage
  input  logic        wb_ready_i        // WB stage is ready for new data
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
  // TODO:OK May reduce to a single bit after moving dret jump to WB
  logic single_step_halt_if_n;
  logic single_step_halt_if_q; // Halting IF after issuing one insn in single step mode
  logic single_step_issue_n;
  logic single_step_issue_q; // Signals when a single step fetch is expected

  
  // Events in ID
  logic jump_taken_id;

  // Events in EX
  logic branch_taken_ex;
  
  // Events in WB
  logic exception_in_wb;
  logic [4:0] exception_cause_wb;
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
  // TODO:OK Add flag for exception_allowed
  logic interrupt_allowed;
  logic debug_allowed;
  logic single_step_allowed;
  
// Data request has been clocked without insn moving to WB
  logic data_req_q;

  logic [4:0] exc_cause; // id of taken interrupt

  // Mux selector for vectored IRQ PC
  assign ctrl_fsm_o.m_exc_vec_pc_mux = (mtvec_mode_i == 2'b0) ? 5'h0 : exc_cause;
    
  assign ctrl_fsm_o.is_decoding = 1'b1; //TODO: May be removed, never driven to 1'b0
  
  ////////////////////////////////////////////////////////////////////

  // ID stage
  // A jump is taken in ID for jump instructions, and also for mret instructions
  assign jump_taken_id  = ((ctrl_transfer_insn_raw_i == BRANCH_JALR) || (ctrl_transfer_insn_raw_i == BRANCH_JAL) ||
                        mret_id_i) && if_id_pipe_i.instr_valid && !jr_stall_i;

  // EX stage 
  // Branch taken for valid branch instructions in EX with valid decision
  assign branch_taken_ex = id_ex_pipe_i.branch_in_ex && id_ex_pipe_i.instr_valid && branch_decision_ex_i;

  // TODO:OK: Add missing exception types
  // Exception in WB if the following evaluates to 1
  assign exception_in_wb = ((ex_wb_pipe_i.instr.mpu_status != MPU_OK) ||
                            ex_wb_pipe_i.instr.bus_resp.err           ||
                            ex_wb_pipe_i.illegal_insn                 ||
                            ex_wb_pipe_i.ecall_insn                   ||
                            ex_wb_pipe_i.ebrk_insn) && ex_wb_pipe_i.instr_valid;
                            
                            
  // Set exception cause
  assign exception_cause_wb = ex_wb_pipe_i.instr.mpu_status != MPU_OK ? EXC_CAUSE_INSTR_FAULT     :
                              ex_wb_pipe_i.instr.bus_resp.err         ? EXC_CAUSE_INSTR_BUS_FAULT :
                              ex_wb_pipe_i.illegal_insn               ? EXC_CAUSE_ILLEGAL_INSN    :
                              ex_wb_pipe_i.ecall_insn                 ? EXC_CAUSE_ECALL_MMODE     :
                              EXC_CAUSE_BREAKPOINT;

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
  assign trigger_match_in_wb = ex_wb_pipe_i.trigger_match && ex_wb_pipe_i.instr_valid;

  // Pending NMI
  assign pending_nmi = 1'b0;

  // Debug //

  // Single step will need to finish insn in WB, including LSU
  // Need to check for finished multicycle instructions, avoiding rvalid (would cause path to instr_o)
  assign single_step_allowed = !(id_ex_pipe_i.lsu_misaligned && id_ex_pipe_i.instr_valid) && !data_req_q;
                             
  
  assign pending_single_step = !debug_mode_q && debug_single_step_i && ex_wb_pipe_i.instr_valid;

  // Regular debug will kill insn in WB, do not allow for LSU in WB as insn must finish with rvalid
  assign debug_allowed = !(ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid) && !data_req_q;// &&
                          //!(id_ex_pipe_i.lsu_misaligned && id_ex_pipe_i.instr_valid));

  assign pending_debug = (trigger_match_in_wb && !debug_mode_q) ||
                         (((debug_req_i || debug_req_q) && !debug_mode_q)      || // External request
                         (ebreak_in_wb && debug_ebreakm_i && !debug_mode_q)   || // Ebreak with dcsr.ebreakm==1
                         //pending_single_step                                  || // single stepping, dcsr.step==1
                          (ebreak_in_wb && debug_mode_q)) && !id_ex_pipe_i.lsu_misaligned;

                           

  assign ctrl_fsm_o.debug_cause = (trigger_match_in_wb && !debug_mode_q)          ? DBG_CAUSE_TRIGGER :
                                  (ebreak_in_wb && !debug_mode_q)                 ? DBG_CAUSE_EBREAK  :
                                  ((debug_req_i || debug_req_q) && !debug_mode_q) ? DBG_CAUSE_HALTREQ :
                                  DBG_CAUSE_STEP;

  // TODO:OK: May allow interuption of Zce to idempotent memories
  assign pending_interrupt = irq_req_ctrl_i && !debug_mode_q;

  // Allow interrupts to be taken only if there is no data request in WB, 
  // and no data_req has been clocked from EX to environment.
  // LSU instructions which were suppressed due to previous exceptions
  // will be interruptable as they did not cause bus access in EX.
  assign interrupt_allowed = ((!(ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid) && !data_req_q &&
                              !id_ex_pipe_i.lsu_misaligned) ||
                               exception_in_wb) && !debug_mode_q; // TODO:OK: Just use instr bus_err/mpu_err/illegal_insn

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

    // By default, no stages are halted
    // If is halted if an insn has been issued during single step
    // to avoid more than one instructions passing down the pipe.
    ctrl_fsm_o.halt_if = single_step_halt_if_q;
    ctrl_fsm_o.halt_id = 1'b0;
    ctrl_fsm_o.halt_ex = 1'b0;
    ctrl_fsm_o.halt_wb = 1'b0;

    // By default no stages are killed
    ctrl_fsm_o.kill_if = 1'b0;
    ctrl_fsm_o.kill_id = 1'b0;
    ctrl_fsm_o.kill_ex = 1'b0;
    ctrl_fsm_o.kill_wb = 1'b0;

    ctrl_fsm_o.csr_restore_mret    = 1'b0;
    ctrl_fsm_o.csr_restore_dret    = 1'b0;
    ctrl_fsm_o.csr_save_if         = 1'b0;
    ctrl_fsm_o.csr_save_id         = 1'b0;
    ctrl_fsm_o.csr_save_ex         = 1'b0;
    ctrl_fsm_o.csr_save_wb         = 1'b0;
    ctrl_fsm_o.csr_save_cause      = 1'b0;
    ctrl_fsm_o.csr_cause           = '0;

    ctrl_fsm_o.exc_pc_mux          = EXC_PC_IRQ;
    exc_cause             = '0; // TODO: Explicit width

    debug_mode_n          = debug_mode_q;
    ctrl_fsm_o.debug_csr_save      = 1'b0;
    ctrl_fsm_o.block_data_addr     = 1'b0;
    
    //Single step halting of IF TODO:OK: May optimize this to a single bit
    single_step_halt_if_n = single_step_halt_if_q;
    single_step_issue_n   = single_step_issue_q;
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
        // NMI // TODO:OK: Implement
        if (pending_nmi) begin
        // Debug entry (except single step which is handled later)
        end else if (pending_debug) begin
          if (debug_allowed) begin
            // Halt the whole pipeline
            ctrl_fsm_o.halt_if = 1'b1;
            ctrl_fsm_o.halt_id = 1'b1;
            ctrl_fsm_o.halt_ex = 1'b1; // TODO: Assert halt_Ex |-> !ex_ready && suppresses not yet stared LOAD/STORES
            ctrl_fsm_o.halt_wb = 1'b1;

            ctrl_fsm_ns = DEBUG_TAKEN;
          end else begin
            // Halt ID to allow debug @bubble later
            ctrl_fsm_o.halt_id = 1'b1;
          end
        // IRQ
        end else if (pending_interrupt) begin
          if (interrupt_allowed) begin
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
            ctrl_fsm_o.csr_cause       = {1'b1,irq_id_ctrl_i};

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
              single_step_issue_n = 1'b1;
              single_step_halt_if_n = 1'b0;
            end
          end else begin // !interrupt_allowed
            // Halt ID to allow interrupt @bubble later
            ctrl_fsm_o.halt_id = 1'b1; // TODO: Halt ID or EX?, to prevent new insn issue
          end
        end else begin
          if (exception_in_wb) begin
            // TODO:OK: Must check if we are allowed to take exceptions
            //          Applies to PMA/PMP on misaligned
            // Kill all stages
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            ctrl_fsm_o.kill_wb = 1'b1;

            // Set pc to exception handler
            ctrl_fsm_o.pc_set       = 1'b1;
            ctrl_fsm_o.pc_mux       = PC_EXCEPTION;
            ctrl_fsm_o.exc_pc_mux   = debug_mode_q ? EXC_PC_DBE : EXC_PC_EXCEPTION;

            // Save CSR from WB
            ctrl_fsm_o.csr_save_wb     = 1'b1;
            ctrl_fsm_o.csr_save_cause  = !debug_mode_q; // Do not update CSRs if in debug mode
            ctrl_fsm_o.csr_cause       = {1'b0, exception_cause_wb};
          // Special insn
          end else if (wfi_in_wb) begin
            // Not halting EX/WB to allow insn (interruptible bubble) in EX to pass to WB before sleeping
            if (!debug_mode_q) begin
              ctrl_fsm_o.halt_if = 1'b1;
              ctrl_fsm_o.halt_id = 1'b1;
              ctrl_fsm_o.instr_req = 1'b0;
              ctrl_fsm_ns = SLEEP;
            end
          end else if (fencei_in_wb) begin
            // Kill all instructions and set pc to wb.pc + 4
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            ctrl_fsm_o.pc_set  = 1'b1;
            ctrl_fsm_o.pc_mux  = PC_FENCEI;

            //TODO:OK: Drive fence.i interface
          end else if (dret_in_wb) begin
            // Dret takes jump from WB stage
            // Kill previous stages and jump to pc in dpc
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;
            ctrl_fsm_o.kill_ex = 1'b1;
            
            ctrl_fsm_o.pc_mux      = PC_DRET;
            ctrl_fsm_o.pc_set      = 1'b1;

            ctrl_fsm_o.csr_restore_dret  = 1'b1; //TODO:OK: Rename to csr_restore_dret_wb_o
            single_step_issue_n = debug_single_step_i; // Expect single step issue
            debug_mode_n  = 1'b0;
          
          end else if (branch_taken_ex) begin // todo: seems like branch might get taken multiple times if preceded by stalling load/store
            ctrl_fsm_o.kill_if = 1'b1;
            ctrl_fsm_o.kill_id = 1'b1;  

            ctrl_fsm_o.pc_mux   = PC_BRANCH;
            ctrl_fsm_o.pc_set   = 1'b1;
            
          end else if (jump_taken_id) begin
            // kill_if
            ctrl_fsm_o.kill_if = 1'b1;

            // Jumps in ID (JAL, JALR, mret, uret, dret)
            if (mret_id_i) begin
              ctrl_fsm_o.pc_mux      = debug_mode_q ? PC_EXCEPTION : PC_MRET;
              ctrl_fsm_o.pc_set      = 1'b1; //TODO:OK: Could have a CSR write to mepc previous to this, add stall/bypass.
              ctrl_fsm_o.exc_pc_mux  = EXC_PC_DBE; // Only used in debug mode
            end else begin
              ctrl_fsm_o.pc_mux = PC_JUMP;
              ctrl_fsm_o.pc_set = 1'b1;
            end
          end

          // Mret in WB restores CSR regs
          // 
          if (mret_in_wb && !ctrl_fsm_o.kill_wb) begin
            ctrl_fsm_o.csr_restore_mret  = !debug_mode_q; // TODO:OK: Rename to csr_restore_mret_wb_o
          end

          // Single step debug entry
          // Need to be after exception/interrupt handling
          // to ensure mepc and if_pc set correctly for use in dpc
          if (pending_single_step) begin
            if (single_step_allowed) begin
              ctrl_fsm_ns = DEBUG_TAKEN;
            end
          end

          // Detect first insn issue in single step after dret
          // Used to block further issuing
          if(single_step_issue_q && (if_valid_i && if_ready_i)) begin
            single_step_halt_if_n = 1'b1;
            single_step_issue_n = 1'b0;
          end
        end // !debug or interrupts
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
        single_step_issue_n   = 1'b0;

        // Kill stages
        ctrl_fsm_o.kill_if = 1'b1; // Needed regardless of single_step, to invalidate alignment_buffer
        ctrl_fsm_o.kill_id = !debug_single_step_i; // Should not be anything to kill for single step
        ctrl_fsm_o.kill_ex = !debug_single_step_i; // Should not be anything to kill for single step
        ctrl_fsm_o.kill_wb = !debug_single_step_i; // Do not kill WB for single step

        // Set pc
        ctrl_fsm_o.pc_set     = 1'b1;
        ctrl_fsm_o.pc_mux     = PC_EXCEPTION;
        ctrl_fsm_o.exc_pc_mux = EXC_PC_DBD;

        // Save CSRs
        ctrl_fsm_o.csr_save_cause = !(ebreak_in_wb && debug_mode_q);  // No CSR update for ebreak in debug mode
        ctrl_fsm_o.debug_csr_save = 1'b1;

        if (debug_single_step_i) begin
          // Single step
          // Should use pc from IF (next insn, as if is halted after first issue)
          // Exception for single step + ebreak, as addr of ebreak (in WB) shall be stored
             // or trigger match, as timing=0 permits us from executing triggered insn before 
             // entering debug mode
          if((ebreak_in_wb && debug_ebreakm_i) || trigger_match_in_wb) begin
            ctrl_fsm_o.csr_save_wb = 1'b1;
          end else begin
            ctrl_fsm_o.csr_save_if = 1'b1;
          end
        end else begin
          // Save pc from oldest valid instruction
          if (ex_wb_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_wb = 1'b1;
          end else if (id_ex_pipe_i.instr_valid && !id_ex_pipe_i.lsu_misaligned) begin
            ctrl_fsm_o.csr_save_ex = 1'b1;
          end else if (if_id_pipe_i.instr_valid) begin
            ctrl_fsm_o.csr_save_id = 1'b1;
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
    end else begin
      ctrl_fsm_cs <= ctrl_fsm_ns;
      debug_mode_q <= debug_mode_n;
    end
  end

  assign ctrl_fsm_o.debug_mode = debug_mode_q;

  // Detect when data_req has been clocked, and lsu insn is still in EX
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      data_req_q <= 1'b0;
    end else begin
      if (data_req_i && !(ex_valid_i && wb_ready_i)) begin
        data_req_q <= 1'b1;
      end else if (ex_valid_i && wb_ready_i) begin
        data_req_q <= 1'b0;
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

  // Flops used to gate if_valid after one instruction issued
  // in single step mode
  // TODO:OK May reduce to one flop after moving dret jump to WB
  always_ff @(posedge clk_ungated_i, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      single_step_halt_if_q <= 1'b0;
      single_step_issue_q   <= 1'b0;
    end else begin
      single_step_halt_if_q <= single_step_halt_if_n;
      single_step_issue_q   <= single_step_issue_n;
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
