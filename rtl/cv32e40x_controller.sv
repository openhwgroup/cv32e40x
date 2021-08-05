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

  input  logic        if_valid_i,
  input  logic        if_ready_i,
  
  // from IF/ID pipeline
  input  if_id_pipe_t if_id_pipe_i,
  input  logic        mret_id_i,
  input  logic        dret_id_i,
  input  logic        csr_en_id_i,
  input  csr_opcode_e csr_op_id_i,

  input  id_ex_pipe_t id_ex_pipe_i,
  input  ex_wb_pipe_t ex_wb_pipe_i,

  // LSU
  input  logic        lsu_misaligned_i, // todo:ab proper postfix
  input  logic        lsu_err_wb_i,               // LSU bus error in WB stage
  input  logic [31:0] lsu_addr_wb_i,              // LSU address in WB stage

  // jump/branch signals
  input  logic        branch_decision_ex_i,       // branch decision signal from EX ALU
  input  logic [1:0]  ctrl_transfer_insn_i,       // jump is being calculated in ALU
  input  logic [1:0]  ctrl_transfer_insn_raw_i,   // jump is being calculated in ALU

  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,
  input  logic [4:0]  irq_id_ctrl_i,
  input  logic        irq_wu_ctrl_i,
  input  PrivLvl_t    current_priv_lvl_i,

  input logic  [1:0]     mtvec_mode_i,

  // Debug Signal
  input  logic         debug_req_i,
  input  logic         debug_single_step_i,
  input  logic         debug_ebreakm_i,
  input  logic         debug_trigger_match_id_i,

  // Regfile target
  input  logic         regfile_alu_we_id_i,        // currently decoded we enable

  // CSR raddr in ex
  input  csr_num_e     csr_raddr_ex_i,

  input rf_addr_t      rf_waddr_ex_i,
  input rf_addr_t      rf_waddr_wb_i,

  input logic [REGFILE_NUM_READ_PORTS-1:0]         rf_re_i,
  input rf_addr_t     rf_raddr_i[REGFILE_NUM_READ_PORTS],
  input rf_addr_t     rf_waddr_i,

  input  logic        id_ready_i,               // ID stage is ready
  input  logic        ex_valid_i,               // EX stage is done
  input  logic        wb_ready_i,               // WB stage is ready
  input  logic        wb_valid_i,                // WB stage is done

  input  logic        obi_data_req_i,           // OBI bus data request (EX) // todo: Should look at 'trans' (goal (please check if true) it to not break a multicycle LSU instruction or already committed load/store; that cannot be judged by only looking at the OBI signals)

  // Outputs
  output ctrl_byp_t   ctrl_byp_o,
  output ctrl_fsm_t   ctrl_fsm_o                // FSM outputs
);

  // Main FSM and debug FSM
  cv32e40x_controller_fsm controller_fsm_i
  (
    // Clocks and reset
    .clk                         ( clk                      ),
    .clk_ungated_i               ( clk_ungated_i            ),
    .rst_n                       ( rst_n                    ),
  
    .fetch_enable_i              ( fetch_enable_i           ),

    .ctrl_byp_i                  ( ctrl_byp_o               ),

    .if_valid_i                  ( if_valid_i               ),
    .if_ready_i                  ( if_ready_i               ),
  
    // From ID stage
    .id_ready_i                  ( id_ready_i               ),
    .if_id_pipe_i                ( if_id_pipe_i             ),
    .mret_id_i                   ( mret_id_i                ),
    .dret_id_i                   ( dret_id_i                ),
    .ex_wb_pipe_i                ( ex_wb_pipe_i             ),
    .ctrl_transfer_insn_i        ( ctrl_transfer_insn_i     ),
    .ctrl_transfer_insn_raw_i    ( ctrl_transfer_insn_raw_i ),

    // From EX stage
    .id_ex_pipe_i                ( id_ex_pipe_i             ),
    .branch_decision_ex_i        ( branch_decision_ex_i     ),
    .ex_valid_i                  ( ex_valid_i               ),
    .obi_data_req_i              ( obi_data_req_i           ),

    // From WB stage
    .lsu_err_wb_i                ( lsu_err_wb_i             ),
    .lsu_addr_wb_i               ( lsu_addr_wb_i            ),
    .wb_ready_i                  ( wb_ready_i               ),
    .wb_valid_i                  ( wb_valid_i               ),

    // Interrupt Controller Signals
    .irq_req_ctrl_i              ( irq_req_ctrl_i           ),
    .irq_id_ctrl_i               ( irq_id_ctrl_i            ),
    .irq_wu_ctrl_i               ( irq_wu_ctrl_i            ),
    .current_priv_lvl_i          ( current_priv_lvl_i       ),
  
    .mtvec_mode_i                ( mtvec_mode_i             ),
  
    // Debug Signal
    .debug_req_i                 ( debug_req_i              ),
    .debug_single_step_i         ( debug_single_step_i      ),
    .debug_ebreakm_i             ( debug_ebreakm_i          ),
    .debug_trigger_match_id_i    ( debug_trigger_match_id_i ),

    // Outputs
    .ctrl_fsm_o                  ( ctrl_fsm_o               )
  );
  

  // Hazard/bypass/stall control instance
  cv32e40x_controller_bypass bypass_i
  (
    // From controller_fsm
    .if_id_pipe_i               ( if_id_pipe_i             ),
    .id_ex_pipe_i               ( id_ex_pipe_i             ),
    .ex_wb_pipe_i               ( ex_wb_pipe_i             ),
    // From decoder
    .ctrl_transfer_insn_raw_i   ( ctrl_transfer_insn_raw_i ),
    .rf_re_i                    ( rf_re_i                  ),
    .rf_raddr_i                 ( rf_raddr_i               ),
    .rf_waddr_i                 ( rf_waddr_i               ),

    // From id_stage
    .regfile_alu_we_id_i        ( regfile_alu_we_id_i      ),
    .mret_id_i                  ( mret_id_i                ),
    .dret_id_i                  ( dret_id_i                ),
    .csr_en_id_i                ( csr_en_id_i              ),
    .csr_op_id_i                ( csr_op_id_i              ),
    .debug_trigger_match_id_i   ( debug_trigger_match_id_i ),

    // From EX
    .rf_waddr_ex_i              ( rf_waddr_ex_i            ),
    .csr_raddr_ex_i             ( csr_raddr_ex_i           ),

    // From WB
    .rf_waddr_wb_i              ( rf_waddr_wb_i            ),
    .wb_ready_i                 ( wb_ready_i               ),

    // From LSU
    .lsu_misaligned_i           ( lsu_misaligned_i         ),

    // Outputs
    .ctrl_byp_o                 ( ctrl_byp_o               )
  );

endmodule // cv32e40x_controller
