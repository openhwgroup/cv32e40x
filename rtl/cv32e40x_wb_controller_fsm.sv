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
// Design Name:    cv32e40x_wb_controller_fsm                                 //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    FSM of the pipeline controller                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_wb_controller_fsm import cv32e40x_pkg::*;
  (
    // Clocks and reset
    input  logic        clk,                        // Gated clock
    input  logic        clk_ungated_i,              // Ungated clock
    input  logic        rst_n,
  
    input  logic        fetch_enable_i,             // Start the decoding
    output logic        ctrl_busy_o,                // Core is busy processing instructions
    output logic        is_decoding_o,              // Core is in decoding state

    // From bypass logic
    input  logic        jr_stall_i,                 // There is a jr-stall pending
    // to IF stage
    output logic        instr_req_o,                // Start fetching instructions
    output logic        pc_set_o,                   // jump to address set by pc_mux
    output pc_mux_e     pc_mux_o,                   // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
    output exc_pc_mux_e exc_pc_mux_o,               // Selects target PC for exception
  
    // From ID stage
    input  logic        id_ready_i,                 // ID stage is ready
    input  if_id_pipe_t if_id_pipe_i,
    input  logic        mret_id_i,                  // mret in ID stage
    input  logic        dret_id_i,                  // dret in ID stage

    // From WB stage
    input  ex_wb_pipe_t ex_wb_pipe_i,

    // From decoder
    input  logic        csr_status_i,               // decoder encountered an csr status instruction
    input  logic [1:0]  ctrl_transfer_insn_i,       // jump is being calculated in ALU
    input  logic [1:0]  ctrl_transfer_insn_raw_i,   // jump is being calculated in ALU

    // From EX stage
    input  id_ex_pipe_t id_ex_pipe_i,        
    input  logic        branch_taken_ex_i,          // branch taken signal from EX ALU
    input  logic        ex_valid_i,                 // EX stage is done
    input  logic        data_req_i,                 // Data interface trans_valid
  
    // From WB stage
    input  logic        data_err_wb_i,              // LSU caused bus_error in WB stage
    input  logic [31:0] data_addr_wb_i,             // Current LSU address in WB stage
    input  logic        wb_ready_i,                 // WB stage is ready
    input  logic        data_req_wb_i,               // ALU data is written back in WB

    // To WB stage
    output logic        block_data_addr_o,          // To LSU to prevent data_addr_wb_i updates between error and taken NMI

    // LSU input
    input  logic [1:0]  lsu_cnt_i,              // LSU outstanding
    input  logic        data_rvalid_i,

    // Interrupt Controller Signals
    input  logic        irq_req_ctrl_i,         // irq requst
    input  logic [4:0]  irq_id_ctrl_i,          // irq id
    input  logic        irq_wu_ctrl_i,          // irq wakeup control
    input  PrivLvl_t    current_priv_lvl_i,     // Current running priviledge level
  
    output logic        irq_ack_o,              // irq has been taken 
    output logic [4:0]  irq_id_o,               // id of taken irq (to toplevel pins)
  
    output logic [4:0]  exc_cause_o,            // id of taken irq (to IF, EXC_PC_MUX, zeroed if mtvec_mode==0)
  
    // Debug Signal
    output logic         debug_mode_o,           // Flag signalling we are in debug mode
    output logic [2:0]   debug_cause_o,          // cause of debug entry
    output logic         debug_csr_save_o,       // Update debug CSRs
    input  logic         debug_req_i,            // External debug request
    input  logic         debug_single_step_i,    // dcsr.step from cs_registers
    input  logic         debug_ebreakm_i,        // dcsr.ebreakm from cs_registers
    input  logic         debug_trigger_match_i,        // Trigger match from cs_registers
    output logic         debug_wfi_no_sleep_o,   // Debug prevents core from sleeping after WFI
    output logic         debug_havereset_o,      // Signal to external debugger that we have reset
    output logic         debug_running_o,        // Signal to external debugger that we are running (not in debug)
    output logic         debug_halted_o,         // Signal to external debugger that we are halted (in debug mode)
  
    // Wakeup Signal
    output logic        wake_from_sleep_o,       // Wakeup (due to irq or debug)
  
    // CSR signals
    output logic        csr_save_if_o,         // Save PC from IF stage
    output logic        csr_save_id_o,         // Save PC from ID stage
    output logic        csr_save_ex_o,         // Save PC from EX stage (currently unused)
    output logic        csr_save_wb_o,         // Save PC from WB stage
    output logic [5:0]  csr_cause_o,           // CSR cause (saves to mcause CSR)
    output logic        csr_restore_mret_id_o, // Restore CSR due to mret
    output logic        csr_restore_dret_id_o, // Restore CSR due to dret
    output logic        csr_save_cause_o,      // Update CSRs
  
    
    // Halt signals
    output logic        halt_if_o, // Halt IF stage
    output logic        halt_id_o,  // Halt ID stage
    output logic        halt_ex_o, // Halt EX stage
    output logic        halt_wb_o, // Halt WB stage

    // Kill signals
    output logic        kill_if_o,
    output logic        kill_id_o,
    output logic        kill_ex_o,
    output logic        kill_wb_o
  );

   // FSM state encoding
  ctrl_state_e ctrl_fsm_cs, ctrl_fsm_ns;

  // Debug state
  debug_state_e debug_fsm_cs, debug_fsm_ns;

  // jump instruction in decode
  logic jump_in_id;

  // Sticky version of debug_req_i
  logic debug_req_q;

  // Debug mode
  logic debug_mode_n;
  logic debug_mode_q;

  logic single_step_n;
  logic single_step_q;
  
  
  // Events in WB
  logic exception_in_wb;
  logic [5:0] exception_cause_wb;
  logic wfi_in_wb;
  logic fencei_in_wb;
  logic mret_in_wb;
  logic dret_in_wb;
  logic ebreak_in_wb;
  logic pending_nmi;
  logic pending_debug;
  logic pending_single_step;
  logic allow_single_step;
  logic pending_interrupt;

  logic interrupt_allowed;
  logic debug_allowed;

  // Data request has been clocked
  logic data_req_q;
  
  ////////////////////////////////////////////////////////////////////
  // Signals to not break core-v-verif compile (will be changed)
  logic illegal_insn_q;
  
  logic branch_in_id;
  assign is_decoding_o = 1'b1; // TODO:OK: Remove
  
  ////////////////////////////////////////////////////////////////////

  // ID stage
  assign jump_in_id  = ((ctrl_transfer_insn_raw_i == BRANCH_JALR) || (ctrl_transfer_insn_raw_i == BRANCH_JAL) ||
                        mret_id_i || dret_id_i) && if_id_pipe_i.instr_valid;

  // TODO:OK: Add missing exception types
  // Exception in WB if the following evaluates to 1
  assign exception_in_wb = (ex_wb_pipe_i.illegal_insn       ||
                            ex_wb_pipe_i.ebrk_insn          ||
                            ex_wb_pipe_i.ecall_insn         ||
                            ex_wb_pipe_i.instr.bus_resp.err ||
                            (ex_wb_pipe_i.instr.mpu_status != MPU_OK)) && ex_wb_pipe_i.instr_valid;
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

  // Async events pending
  assign pending_nmi = 1'b0;

  // Debug

  assign single_step_n = (ctrl_fsm_cs == DEBUG_TAKEN) ? 1'b0 : pending_single_step;
  assign allow_single_step = debug_allowed;// && !((|lsu_cnt_i) || ((lsu_cnt_i == 2'b1) && data_rvalid_i));

  assign pending_single_step = !debug_mode_q && debug_single_step_i && (ex_wb_pipe_i.instr_valid || single_step_q); // TODO:OK Must wait for rvalid in case of LSU 

  assign debug_allowed = (!(ex_wb_pipe_i.data_req && ex_wb_pipe_i.instr_valid) && !data_req_q &&
                              !(id_ex_pipe_i.data_misaligned && id_ex_pipe_i.instr_valid)); // TODO:OK: Could just use instr bus_err/mpu_err

  assign pending_debug = (((debug_req_i || debug_req_q) && !debug_mode_q)      || // External request
                         (ebreak_in_wb && debug_ebreakm_i && !debug_mode_q)   || // Ebreak with dcsr.ebreakm==1
                         //pending_single_step                                  || // single stepping, dcsr.step==1
                          (ebreak_in_wb && debug_mode_q)) && !id_ex_pipe_i.data_misaligned;

                           

  assign debug_cause_o = (ebreak_in_wb && !debug_mode_q)                 ? DBG_CAUSE_EBREAK :
                         ((debug_req_i || debug_req_q) && !debug_mode_q) ? DBG_CAUSE_HALTREQ :
                         DBG_CAUSE_STEP;

  // TODO:OK: Masking interrupts in case of debug
  // TODO:OK: May allow interuption of Zce to idempotent memories
  assign pending_interrupt = irq_req_ctrl_i;

  // Allow interrupts to be taken only if there is no data request in WB, 
  // and no data_req has been clocked from EX to environment.
  // LSU instructions which were suppressed due to previous exceptions
  // will be interruptable as they did not cause bus access in EX.
  assign interrupt_allowed = ((!(ex_wb_pipe_i.data_req && ex_wb_pipe_i.instr_valid) && !data_req_q &&
                              !id_ex_pipe_i.data_misaligned) ||
                               exception_in_wb) && !debug_mode_q; // TODO:OK: Could just use instr bus_err/mpu_err

  //////////////
  // FSM comb //
  //////////////
  always_comb begin
    // Default values
    ctrl_busy_o = 1'b1;
    ctrl_fsm_ns = ctrl_fsm_cs;
    instr_req_o = 1'b1;

    pc_mux_o = PC_BOOT;
    pc_set_o = 1'b0;

    irq_ack_o = 1'b0;
    irq_id_o  = '0;

    // By default, no stages are halted
    halt_if_o = 1'b0;
    halt_id_o = 1'b0;
    halt_ex_o = 1'b0;
    halt_wb_o = 1'b0;

    // By default no stages are killed
    kill_if_o = 1'b0;
    kill_id_o = 1'b0;
    kill_ex_o = 1'b0;
    kill_wb_o = 1'b0;

    csr_restore_mret_id_o = 1'b0;
    csr_restore_dret_id_o = 1'b0;
    csr_save_if_o         = 1'b0; // TODO:OK May remove if/id/ex
    csr_save_id_o         = 1'b0;
    csr_save_ex_o         = 1'b0;
    csr_save_wb_o         = 1'b0;
    csr_save_cause_o      = 1'b0;
    csr_cause_o           = '0;

    exc_pc_mux_o           = EXC_PC_IRQ;
    exc_cause_o            = '0;

    debug_mode_n          = debug_mode_q;
    debug_csr_save_o      = 1'b0;
    

    unique case (ctrl_fsm_cs)
      RESET: begin
        instr_req_o = 1'b0;
        if ( fetch_enable_i ) begin
          ctrl_fsm_ns = BOOT_SET;
        end
      end
      BOOT_SET: begin
        instr_req_o = 1'b1;
        pc_mux_o    = PC_BOOT;
        pc_set_o    = 1'b1;
        kill_if_o   = 1'b1; // TODO: May remove this
        ctrl_fsm_ns = FUNCTIONAL;
      end
      FUNCTIONAL: begin
        // NMI // TODO:OK: Implement
        if (pending_nmi ) begin
        // Debug entry // TODO:OK Implement
        end else if( pending_debug ) begin
          if( debug_allowed ) begin
            // Kill the whole pipeline
            halt_if_o = 1'b1;
            halt_id_o = 1'b1;
            halt_ex_o = 1'b1;
            halt_wb_o = 1'b1;

            // Proceed to debug TODO:OK We could remove this state, but duplicate code for debug_taken when taking single steps
            ctrl_fsm_ns = DEBUG_TAKEN;
          end else begin
            // Halt ID to allow debug @bubble later
            halt_id_o = 1'b1;
          end
        // IRQ
        end else if( pending_interrupt) begin
          if( interrupt_allowed ) begin
            kill_if_o = 1'b1;
            kill_id_o = 1'b1;
            kill_ex_o = 1'b1;
            kill_wb_o = 1'b1;

            pc_set_o = 1'b1;
            pc_mux_o = PC_EXCEPTION;
            exc_pc_mux_o = EXC_PC_IRQ;
            exc_cause_o = irq_id_ctrl_i;

            irq_ack_o = 1'b1;
            irq_id_o = irq_id_ctrl_i;

            csr_save_cause_o  = 1'b1;
            csr_cause_o       = {1'b1,irq_id_ctrl_i};

            // Save pc from oldest valid instruction
            if(ex_wb_pipe_i.instr_valid ) begin
              csr_save_wb_o = 1'b1;
            end else if( id_ex_pipe_i.instr_valid) begin
              csr_save_ex_o = 1'b1;
            end else if( if_id_pipe_i.instr_valid) begin
              csr_save_id_o = 1'b1;
            end else begin
              csr_save_if_o = 1'b1;
            end
          end else begin // !interrupt_allowed
            // Halt ID to allow interrupt @bubble later
            halt_id_o = 1'b1;
          end
        end else begin
          if (exception_in_wb) begin
            // TODO:OK: Must check if we are allowed to take exceptions

            // Kill all stages
            kill_if_o = 1'b1;//!debug_single_step_i;//1'b1;
            kill_id_o = !debug_single_step_i;//1'b1;
            kill_ex_o = !debug_single_step_i;//1'b1;

            // Set pc to exception handler
            pc_set_o       = 1'b1;
            pc_mux_o       = PC_EXCEPTION;
            exc_pc_mux_o   = debug_mode_q ? EXC_PC_DBE : EXC_PC_EXCEPTION;

            // Save CSR from WB
            csr_save_wb_o     = 1'b1;
            csr_save_cause_o  = !debug_mode_q; // Do not update CSRs if in debug mode
            csr_cause_o       = {1'b0, exception_cause_wb};
          // Special insn
          end else if( wfi_in_wb ) begin
            // TODO:OK: Need to evaluate sleeping based on debug pending etc..
            // Not halting EX/WB to allow insn (interruptible bubble) in EX to pass to WB before sleeping
            if( !debug_mode_q ) begin
              halt_if_o = 1'b1;
              halt_id_o = 1'b1;
              instr_req_o = 1'b0;
              ctrl_fsm_ns = SLEEP;
            end
          end else if ( fencei_in_wb ) begin
            // Kill all instructions and set pc to wb.pc + 4
            kill_if_o = 1'b1;
            kill_id_o = 1'b1;
            kill_ex_o = 1'b1;
            pc_set_o  = 1'b1;
            pc_mux_o  = PC_FENCEI;

            //TODO:OK: Drive fence.i interface
          end else if( branch_taken_ex_i ) begin
            pc_mux_o   = PC_BRANCH;
            pc_set_o   = 1'b1;
            kill_if_o = 1'b1;
            kill_id_o = 1'b1;  
          end else if ( jump_in_id ) begin
            // kill_if
            kill_if_o = 1'b1;
            // Jumps in ID (JAL, JALR, mret, uret, dret)
            if ( mret_id_i ) begin
              pc_mux_o      = debug_mode_q ? PC_EXCEPTION : PC_MRET;
              pc_set_o      = 1'b1;
              exc_pc_mux_o  = EXC_PC_DBE; // Only used in debug mode
            end else if ( dret_id_i ) begin
              pc_mux_o      = PC_DRET;
              pc_set_o      = 1'b1;
            end else begin
              pc_mux_o = PC_JUMP;
              pc_set_o = !jr_stall_i;
            end
          end

          //TODO:OK: Trigger on mret: Should be killed with no side effects
          //         Should this section be part of the if/else block above?
          if ( mret_in_wb ) begin
            csr_restore_mret_id_o = !debug_mode_q; // TODO:OK: Rename to csr_restore_mret_wb_o
          end else if ( dret_in_wb ) begin
            csr_restore_dret_id_o = 1'b1; //TODO:OK: Rename to csr_restore_dret_wb_o
            debug_mode_n  = 1'b0;
          end

          // Single step debug entry
          // Need to be after exception/interrupt handling
          // to ensure mepc and if_pc set correctly for use in dpc
          if( pending_single_step ) begin // ex_wb_pipe.instr_valid is implicit
            
            if( allow_single_step ) begin
              halt_if_o = 1'b1;
              halt_id_o = 1'b1;
              halt_ex_o = 1'b1;
              halt_wb_o = 1'b1;

              ctrl_fsm_ns = DEBUG_TAKEN;
            end else begin
              // Prevent new ins while LSU finishes
              halt_if_o = 1'b1;
              halt_id_o = 1'b1;
              
            end
          end
        end // !debug or interrupts
      end
      SLEEP: begin
        ctrl_busy_o = 1'b0;
        instr_req_o = 1'b0;
        //halt_if_o   = 1'b1;
        //halt_id_o   = 1'b1;
        //halt_ex_o   = 1'b1;
        halt_wb_o   = 1'b1;
        if(wake_from_sleep_o) begin
          ctrl_fsm_ns = FUNCTIONAL;
          ctrl_busy_o = 1'b1;
        end
      end
      DEBUG_TAKEN: begin
        // Kill all stages
        kill_if_o = 1'b1;
        kill_id_o = 1'b1;
        kill_ex_o = 1'b1;
        kill_wb_o = !debug_single_step_i;// Do not kill WB for single step

        // Set pc
        pc_set_o  = 1'b1;
        pc_mux_o  = PC_EXCEPTION;
        exc_pc_mux_o = EXC_PC_DBD;

        // Save CSRs
        csr_save_cause_o = 1'b1;
        debug_csr_save_o = !(ebreak_in_wb && debug_mode_q);

        if( (debug_single_step_i && exception_in_wb) ) begin
          // Single step and exception
          // Should use pc from IF, as a branch to exception handler
          // was performed last cycle
          csr_save_if_o = 1'b1;
        end else begin
          // Save pc from oldest valid instruction
          // Do not save if ebreak in debug mode
          if(ex_wb_pipe_i.instr_valid && !debug_single_step_i) begin
            csr_save_wb_o = !(ebreak_in_wb && debug_mode_q);
          end else if( id_ex_pipe_i.instr_valid && !id_ex_pipe_i.data_misaligned) begin
            csr_save_ex_o = !(ebreak_in_wb && debug_mode_q);
          end else if( if_id_pipe_i.instr_valid) begin
            csr_save_id_o = !(ebreak_in_wb && debug_mode_q);
          end else begin
            csr_save_if_o = !(ebreak_in_wb && debug_mode_q);
          end
        end

        // Enter debug mode next cycle
        debug_mode_n = 1'b1;
        ctrl_fsm_ns = FUNCTIONAL;
      end
      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  // Wakeup from sleep
  assign wake_from_sleep_o = irq_wu_ctrl_i || pending_debug || debug_mode_q;

  ////////////////////
  // Flops          //
  ////////////////////
  always_ff @(posedge clk , negedge rst_n) begin
    if ( rst_n == 1'b0 ) begin
      ctrl_fsm_cs <= RESET;
      debug_mode_q <= 1'b0;
    end else begin
      ctrl_fsm_cs <= ctrl_fsm_ns;
      single_step_q <= single_step_n;
      debug_mode_q <= debug_mode_n;
    end
  end

  // Detect when data_req has been clocked, and lsu insn is still in EX
  always_ff @(posedge clk , negedge rst_n) begin
    if ( rst_n == 1'b0 ) begin
      data_req_q <= 1'b0;
    end else begin
      if(data_req_i && !ex_valid_i) begin
        data_req_q <= 1'b1;
      end else if(ex_valid_i) begin
        data_req_q <= 1'b0;
      end
    end
  end

  // sticky version of debug_req (must be on clk_ungated_i such that incoming pulse before core is enabled is not missed)
  always_ff @(posedge clk_ungated_i, negedge rst_n) begin
    if ( !rst_n ) begin
      debug_req_q <= 1'b0;
    end else begin
      if( debug_req_i ) begin
        debug_req_q <= 1'b1;
      end else if( debug_mode_q ) begin
        debug_req_q <= 1'b0;
      end
    end
  end

  assign debug_mode_o = debug_mode_q;

  
  /////////////////////
  // Debug state FSM //
  /////////////////////
  always_ff @(posedge clk , negedge rst_n) begin
    if ( rst_n == 1'b0 ) begin
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

  assign debug_havereset_o = debug_fsm_cs[HAVERESET_INDEX];
  assign debug_running_o = debug_fsm_cs[RUNNING_INDEX];
  assign debug_halted_o = debug_fsm_cs[HALTED_INDEX];

endmodule //cv32e40x_wb_controller_fsm