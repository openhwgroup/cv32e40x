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

module cv32e40x_controller import cv32e40x_pkg::*;
(
  input  logic        clk,                        // Gated clock
  input  logic        clk_ungated_i,              // Ungated clock
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start the decoding
  output logic        ctrl_busy_o,                // Core is busy processing instructions
  output logic        is_decoding_o,              // Core is in decoding state

  // decoder related signals
  output logic        deassert_we_o,              // deassert write enable for next instruction

  input  logic        illegal_insn_i,             // decoder encountered an invalid instruction
  input  logic        ecall_insn_i,               // decoder encountered an ecall instruction
  input  logic        mret_insn_i,                // decoder encountered an mret instruction

  input  logic        dret_insn_i,                // decoder encountered an dret instruction

  input  logic        wfi_insn_i,                 // decoder wants to execute a WFI
  input  logic        ebrk_insn_i,                // decoder encountered an ebreak instruction
  input  logic        fencei_insn_i,              // decoder encountered an fence.i instruction
  input  logic        csr_status_i,               // decoder encountered an csr status instruction

  
  // from IF/ID pipeline
  input  if_id_pipe_t if_id_pipe_i,

  // from prefetcher
  output logic        instr_req_o,                // Start fetching instructions

  // to prefetcher
  output logic        pc_set_o,                   // jump to address set by pc_mux
  output pc_mux_e     pc_mux_o,                   // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  output exc_pc_mux_e exc_pc_mux_o,               // Selects target PC for exception

 
  // LSU
  input  logic        data_req_ex_i,              // data memory access is currently performed in EX stage
  input  logic        data_we_ex_i,
  input  logic        data_misaligned_i,

  input  logic        data_err_wb_i,              // LSU caused bus_error in WB stage
  input  logic [31:0] data_addr_wb_i,             // Current LSU address in WB stage
  output logic        block_data_addr_o,          // To LSU to prevent data_addr_wb_i updates between error and taken NMI

  // jump/branch signals
  input  logic        branch_taken_ex_i,          // branch taken signal from EX ALU
  input  logic [1:0]  ctrl_transfer_insn_i,       // jump is being calculated in ALU
  input  logic [1:0]  ctrl_transfer_insn_raw_i,   // jump is being calculated in ALU

  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,
  input  logic [4:0]  irq_id_ctrl_i,
  input  logic        irq_wu_ctrl_i,
  input  PrivLvl_t    current_priv_lvl_i,

  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

  input logic  [1:0]     mtvec_mode_i,
  output logic [4:0]     m_exc_vec_pc_mux_o, // Mux selector for vectored IRQ PC
  // Debug Signal
  output logic         debug_mode_o,
  output logic [2:0]   debug_cause_o,
  output logic         debug_csr_save_o,
  input  logic         debug_req_i,
  input  logic         debug_single_step_i,
  input  logic         debug_ebreakm_i,
  input  logic         debug_trigger_match_i,
  output logic         debug_wfi_no_sleep_o,
  output logic         debug_havereset_o,
  output logic         debug_running_o,
  output logic         debug_halted_o,

  // Wakeup Signal
  output logic        wake_from_sleep_o,

  output logic        csr_save_if_o,
  output logic        csr_save_id_o,
  output logic        csr_save_ex_o,
  output logic [5:0]  csr_cause_o,
  output logic        csr_restore_mret_id_o,

  output logic        csr_restore_dret_id_o,

  output logic        csr_save_cause_o,


  // Regfile target
  input  logic           regfile_alu_we_id_i,        // currently decoded we enable

  // Forwarding signals from regfile
  input  logic           rf_we_ex_i,            // Register file write enable from EX stage
  input  logic           rf_we_wb_i,            // Register file write enable from WB stage

  // forwarding signals
  output op_fw_mux_e  operand_a_fw_mux_sel_o,     // regfile ra data selector form ID stage
  output op_fw_mux_e  operand_b_fw_mux_sel_o,     // regfile rb data selector form ID stage
  output jalr_fw_mux_e  jalr_fw_mux_sel_o,          // data selector for jump target

  input rf_addr_t  rf_waddr_ex_i,
  input rf_addr_t  rf_waddr_wb_i,

  input logic [REGFILE_NUM_READ_PORTS-1:0]         rf_re_i,
  input rf_addr_t  rf_raddr_i[REGFILE_NUM_READ_PORTS],
  input rf_addr_t  rf_waddr_i,


  // stall signals
  output logic        halt_if_o,
  output logic        halt_id_o,

  output logic        kill_if_o,

  output logic        misaligned_stall_o,
  output logic        jr_stall_o,
  output logic        load_stall_o,

  input  logic        id_ready_i,                 // ID stage is ready
  
  input  logic        ex_valid_i,                 // EX stage is done

  input  logic        wb_ready_i,                 // WB stage is ready

  input  logic        data_req_wb_i               // ALU data is written back in WB
);

  logic [4:0]         exc_cause;

  // Mux selector for vectored IRQ PC
  assign m_exc_vec_pc_mux_o = (mtvec_mode_i == 2'b0) ? 5'h0 : exc_cause;
  
  // Main FSM and debug FSM
`ifndef CV32E40X_WB_CONTROLLER
  cv32e40x_controller_fsm
`else
  cv32e40x_wb_controller_fsm
`endif
  controller_fsm_i (
    // Clocks and reset
    .clk                         ( clk           ),
    .clk_ungated_i               ( clk_ungated_i ),
    .rst_n,
  
    .fetch_enable_i              ( fetch_enable_i ),
    .ctrl_busy_o                 ( ctrl_busy_o    ),
    .is_decoding_o               ( is_decoding_o  ),

    .jr_stall_i                  ( jr_stall_o     ),

    // to IF stage
    .instr_req_o                 ( instr_req_o    ),
    .pc_set_o                    ( pc_set_o       ),
    .pc_mux_o                    ( pc_mux_o       ),
    .exc_pc_mux_o                ( exc_pc_mux_o   ),
  
    // From ID stage
    .id_ready_i                  ( id_ready_i     ),
    .if_id_pipe_i                ( if_id_pipe_i   ),

    // From decoder
    .illegal_insn_i              ( illegal_insn_i ),
    .ecall_insn_i                ( ecall_insn_i   ),
    .mret_insn_i                 ( mret_insn_i    ),
    .dret_insn_i                 ( dret_insn_i    ),
    .wfi_insn_i                  ( wfi_insn_i     ),
    .ebrk_insn_i                 ( ebrk_insn_i    ),
    .fencei_insn_i               ( fencei_insn_i  ),
    .csr_status_i                ( csr_status_i   ),
    .ctrl_transfer_insn_i        ( ctrl_transfer_insn_i     ),
    .ctrl_transfer_insn_raw_i    ( ctrl_transfer_insn_raw_i ),

    // From EX stage
    .branch_taken_ex_i           ( branch_taken_ex_i        ),
    .ex_valid_i                  ( ex_valid_i               ),
  
    // From WB stage
    .data_err_wb_i               ( data_err_wb_i            ),
    .data_addr_wb_i              ( data_addr_wb_i           ),
    .wb_ready_i                  ( wb_ready_i               ),
    .data_req_wb_i               ( data_req_wb_i            ),

    // To WB stage
    .block_data_addr_o           ( block_data_addr_o        ),

    // Interrupt Controller Signals
    .irq_req_ctrl_i              ( irq_req_ctrl_i           ),
    .irq_id_ctrl_i               ( irq_id_ctrl_i            ),
    .irq_wu_ctrl_i               ( irq_wu_ctrl_i            ),
    .current_priv_lvl_i          ( current_priv_lvl_i       ),
  
    .irq_ack_o                   ( irq_ack_o                ),
    .irq_id_o                    ( irq_id_o                 ),
  
    .exc_cause_o                 ( exc_cause                ),
  
    // Debug Signal
    .debug_mode_o                ( debug_mode_o             ),
    .debug_cause_o               ( debug_cause_o            ),
    .debug_csr_save_o            ( debug_csr_save_o         ),
    .debug_req_i                 ( debug_req_i              ),
    .debug_single_step_i         ( debug_single_step_i      ),
    .debug_ebreakm_i             ( debug_ebreakm_i          ),
    .debug_trigger_match_i       ( debug_trigger_match_i    ),
    .debug_wfi_no_sleep_o        ( debug_wfi_no_sleep_o     ),
    .debug_havereset_o           ( debug_havereset_o        ),
    .debug_running_o             ( debug_running_o          ),
    .debug_halted_o              ( debug_halted_o           ),
  
    // Wakeup Signal
    .wake_from_sleep_o           ( wake_from_sleep_o        ),
  
    // CSR signals
    .csr_save_if_o               ( csr_save_if_o            ),
    .csr_save_id_o               ( csr_save_id_o            ),
    .csr_save_ex_o               ( csr_save_ex_o            ),
    .csr_cause_o                 ( csr_cause_o              ),
    .csr_restore_mret_id_o       ( csr_restore_mret_id_o    ),
    .csr_restore_dret_id_o       ( csr_restore_dret_id_o    ),
    .csr_save_cause_o            ( csr_save_cause_o         ),
  
    
    // Halt signals
    .halt_if_o                   ( halt_if_o                ),
    .halt_id_o                   ( halt_id_o                ),
    .kill_if_o                   ( kill_if_o                )
  );
  

  // Hazard/bypass/stall control instance
  cv32e40x_controller_bypass bypass_i (
    
      // From controller_fsm
      .is_decoding_i              ( is_decoding_o            ),
    
      // From decoder
      .ctrl_transfer_insn_raw_i   ( ctrl_transfer_insn_raw_i ),
      .rf_re_i                    ( rf_re_i                  ),
      .rf_raddr_i                 ( rf_raddr_i               ),
      .rf_waddr_i                 ( rf_waddr_i               ),
  
      // From id_stage
      .regfile_alu_we_id_i        ( regfile_alu_we_id_i      ),
    
      // From EX
      .rf_we_ex_i                 ( rf_we_ex_i               ),
      .rf_waddr_ex_i              ( rf_waddr_ex_i            ),
      .data_req_ex_i              ( data_req_ex_i            ),
      
      // From WB
      .rf_we_wb_i                 ( rf_we_wb_i               ),
      .rf_waddr_wb_i              ( rf_waddr_wb_i            ),
      .wb_ready_i                 ( wb_ready_i               ),
      .data_req_wb_i              ( data_req_wb_i            ),
  
      // From LSU
      .data_misaligned_i          ( data_misaligned_i        ),
    
      // forwarding mux sel outputs
      .operand_a_fw_mux_sel_o     ( operand_a_fw_mux_sel_o   ),
      .operand_b_fw_mux_sel_o     ( operand_b_fw_mux_sel_o   ),
      .jalr_fw_mux_sel_o          ( jalr_fw_mux_sel_o        ),
  
      // Stall outputs  
      .misaligned_stall_o         ( misaligned_stall_o       ),
      .jr_stall_o                 ( jr_stall_o               ),
      .load_stall_o               ( load_stall_o             ),
  
      // To decoder
      .deassert_we_o              ( deassert_we_o            )
    
    );

endmodule // cv32e40x_controller
