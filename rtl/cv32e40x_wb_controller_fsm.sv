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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Robert Balas - balasr@iis.ee.ethz.ch                       //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Design Name:    Main controller                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor                       //
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

    // From WB stage
    input  ex_wb_pipe_t ex_wb_pipe_i,

    // From decoder
    input  logic        csr_status_i,               // decoder encountered an csr status instruction
    input  logic [1:0]  ctrl_transfer_insn_i,       // jump is being calculated in ALU
    input  logic [1:0]  ctrl_transfer_insn_raw_i,   // jump is being calculated in ALU

    // From EX stage
    input  logic        branch_taken_ex_i,          // branch taken signal from EX ALU
    input  logic        ex_valid_i,                 // EX stage is done
  
    // From WB stage
    input  logic        data_err_wb_i,              // LSU caused bus_error in WB stage
    input  logic [31:0] data_addr_wb_i,             // Current LSU address in WB stage
    input  logic        wb_ready_i,                 // WB stage is ready
    input  logic        data_req_wb_i,               // ALU data is written back in WB

    // To WB stage
    output logic        block_data_addr_o,          // To LSU to prevent data_addr_wb_i updates between error and taken NMI

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

    // Kill signals
    output logic        kill_if_o,
    output logic        kill_id_o,
    output logic        kill_ex_o
  );

   // FSM state encoding
  ctrl_state_e ctrl_fsm_cs, ctrl_fsm_ns;

  // Debug state
  debug_state_e debug_fsm_cs, debug_fsm_ns;

  // jump instruction in decode
  logic jump_in_dec;

  // Sticky version of debug_req_i
  logic debug_req_q;

  // Debug mode
  logic debug_mode_n;
  logic debug_mode_q;
  assign debug_mode_q = 1'b0; // TODO:OK: Implement when debug mode is implemented

  // Exception in WB
  logic exception_in_wb;
  logic [5:0] exception_cause_wb;

  ////////////////////////////////////////////////////////////////////
  // Signals to not break core-v-verif compile (will be changed)
  logic illegal_insn_q;
  logic debug_req_pending;
  logic branch_in_id;
  assign is_decoding_o = 1'b1; // TODO:OK: Remove
  ////////////////////////////////////////////////////////////////////

  // Exception in WB if the following evaluates to 1
  assign exception_in_wb = (ex_wb_pipe_i.illegal_insn   ||
                            ex_wb_pipe_i.ebrk_insn      ||
                            ex_wb_pipe_i.ecall_insn)    && ex_wb_pipe_i.instr_valid;
  // Set exception cause
  assign exception_cause_wb = ex_wb_pipe_i.illegal_insn ? EXC_CAUSE_ILLEGAL_INSN :
                              ex_wb_pipe_i.ecall_insn  ? EXC_CAUSE_ECALL_MMODE   :
                              EXC_CAUSE_BREAKPOINT;
                              

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

    jump_in_dec            = (ctrl_transfer_insn_raw_i == BRANCH_JALR) || (ctrl_transfer_insn_raw_i == BRANCH_JAL);

    kill_if_o = 1'b0;
    kill_id_o = 1'b0;
    kill_ex_o = 1'b0;

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

    debug_mode_o          = 1'b0; // TODO:OK Set properly when debug mode is implemented
    // Signals that may change
    halt_if_o = 1'b0;
    halt_id_o = 1'b0;
    

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
        // NMI
        // Debug entry
        // IRQ
        // Exceptions
        if (exception_in_wb) begin
          // TODO:OK: Must check if we are allowed to take exceptions

          // Kill all stages
          kill_if_o = 1'b1;
          kill_id_o = 1'b1;
          kill_ex_o = 1'b1;
          // Set pc to exception handler
          pc_set_o       = 1'b1;
          pc_mux_o       = PC_EXCEPTION;
          exc_pc_mux_o   = EXC_PC_EXCEPTION;  // TODO:OK: Take in account debug mode
          // Save CSR from WB
          csr_save_wb_o     = 1'b1;
          csr_save_cause_o  = !debug_mode_q;
          csr_cause_o       = {1'b0, exception_cause_wb};
        // Special insn
        end else if( ex_wb_pipe_i.wfi_insn && ex_wb_pipe_i.instr_valid ) begin
          // TODO:OK: Implemented for sleeping to end simulations properly.
          //          Need to evaluate sleeping based on debug pending etc..
          kill_if_o = 1'b1;
          kill_id_o = 1'b1;
          kill_ex_o = 1'b1;
          instr_req_o = 1'b0;
          ctrl_fsm_ns = SLEEP;
        end else if ( ex_wb_pipe_i.fencei_insn && ex_wb_pipe_i.instr_valid ) begin
          // Kill all instructions and set pc wo wb.pc + 4
          kill_if_o = 1'b1;
          kill_id_o = 1'b1;
          kill_ex_o = 1'b1;
          pc_set_o  = 1'b1;
          pc_mux_o  = PC_FENCEI;
        // Single step debug entry
        // Branch taken in EX (bne, beq, blt(u), bge(u))
        end else if( branch_taken_ex_i ) begin // && id_ex_pipe.instr_valid
          pc_mux_o   = PC_BRANCH;
          pc_set_o   = 1'b1;
          kill_if_o = 1'b1;
          kill_id_o = 1'b1;  
        end else if ((jump_in_dec || mret_id_i) && if_id_pipe_i.instr_valid) begin
          // kill_if
          kill_if_o = 1'b1;
          // Jumps in ID (JAL, JALR, mret, uret, dret)
          if ( mret_id_i) begin
            csr_restore_mret_id_o = 1'b1; // TODO:OK: Cannot do this, CSR must be updated in WB
            pc_mux_o              = PC_MRET; // TODO:OK Implement mux for exception if in debug mode
            pc_set_o              = !jr_stall_i;
          end else begin
            pc_mux_o = PC_JUMP;
            pc_set_o = !jr_stall_i;
          end
        end
      end
      SLEEP: begin
        ctrl_busy_o = 1'b0;
        instr_req_o = 1'b0;
      end
    endcase
  end

  ////////////////////
  // Flops          //
  ////////////////////
  always_ff @(posedge clk , negedge rst_n) begin
    if ( rst_n == 1'b0 ) begin
      ctrl_fsm_cs <= RESET;
    end else begin
      ctrl_fsm_cs <= ctrl_fsm_ns;
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