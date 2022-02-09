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
// Engineer        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Decoder                                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_decoder import cv32e40x_pkg::*;
#(
  parameter bit          A_EXT                  = 0,
  parameter b_ext_e      B_EXT                  = B_NONE,
  parameter m_ext_e      M_EXT                  = M,
  parameter              DEBUG_TRIGGER_EN       = 1
)
(
  // singals running to/from controller
  input  logic          deassert_we_i,          // deassert we and special insn (exception in IF)

  output logic          sys_en_o,               // System enable
  output logic          illegal_insn_o,         // Illegal instruction encountered
  output logic          sys_ebrk_insn_o,        // Trap instruction encountered
  output logic          sys_mret_insn_o,        // Return from exception instruction encountered (M)
  output logic          sys_dret_insn_o,        // Return from debug (M)
  output logic          sys_ecall_insn_o,       // Environment call (syscall) instruction encountered
  output logic          sys_wfi_insn_o,         // Pipeline flush is requested
  output logic          sys_fencei_insn_o,      // fence.i instruction

  // from IF/ID pipeline
  input  logic [31:0]   instr_rdata_i,          // Instruction
  input  logic          illegal_c_insn_i,       // Compressed instruction illegal

  // ALU signals
  output logic          alu_en_o,               // ALU enable
  output logic          alu_en_raw_o,           // ALU enable without deassert
  output logic          alu_bch_o,              // ALU branch (ALU used for comparison)
  output logic          alu_jmp_o,              // ALU jump (JALR, JALR) (ALU used to compute LR)
  output logic          alu_jmpr_o,             // ALU jump register (JALR) (ALU used to compute LR)
  output alu_opcode_e   alu_operator_o,         // ALU operation selection
  output alu_op_a_mux_e alu_op_a_mux_sel_o,     // Operand a selection: reg value, PC, immediate or zero
  output alu_op_b_mux_e alu_op_b_mux_sel_o,     // Operand b selection: reg value or immediate

  // MUL related control signals
  output mul_opcode_e   mul_operator_o,         // Multiplication operation selection
  output logic          mul_en_o,               // Perform integer multiplication
  output logic [1:0]    mul_signed_mode_o,      // Multiplication in signed mode
  
  // DIV related control signals
  output div_opcode_e   div_operator_o,         // Division operation selection
  output logic          div_en_o,               // Perform division

  // CSR
  output logic          csr_en_o,               // Enable access to CSR
  output csr_opcode_e   csr_op_o,               // Operation to perform on CSR

  // LSU
  output logic          lsu_en_o,               // Start transaction to data memory
  output logic          lsu_we_o,               // Data memory write enable
  output logic [1:0]    lsu_size_o,             // Data size (byte, half word or word)
  output logic          lsu_sext_o,             // Sign extension on read data from data memory
  output logic [5:0]    lsu_atop_o,             // Atomic memory access

  // Register file related signals
  output logic          rf_we_o,                // Write enable for register file
  output logic [1:0]    rf_re_o,

  // Mux selects
  output op_c_mux_e     op_c_mux_sel_o,         // Operand c selection: reg value or jump target
  output imm_a_mux_e    imm_a_mux_sel_o,        // Immediate selection for operand a
  output imm_b_mux_e    imm_b_mux_sel_o,        // Immediate selection for operand b
  output bch_jmp_mux_e  bch_jmp_mux_sel_o,      // Branch / jump target selection

  input  ctrl_fsm_t     ctrl_fsm_i              // Control signal from controller_fsm
);

  // write enable/request control
  logic       rf_we;
  logic       lsu_en;

  logic       csr_en;
  logic       alu_en;
  logic       mul_en;
  logic       div_en;
  logic       sys_en;

  decoder_ctrl_t decoder_i_ctrl;
  decoder_ctrl_t decoder_m_ctrl;
  decoder_ctrl_t decoder_a_ctrl;
  decoder_ctrl_t decoder_b_ctrl;
  decoder_ctrl_t decoder_ctrl_mux_subdec;
  decoder_ctrl_t decoder_ctrl_mux;

  // RV32I Base instruction set decoder
  cv32e40x_i_decoder
  #(
    .DEBUG_TRIGGER_EN (DEBUG_TRIGGER_EN)
  )
  i_decoder_i
  (
    .instr_rdata_i  ( instr_rdata_i  ),
    .ctrl_fsm_i     ( ctrl_fsm_i     ),
    .decoder_ctrl_o ( decoder_i_ctrl )
  );


  generate
    if (A_EXT) begin: a_decoder
      // RV32A extension decoder
      cv32e40x_a_decoder a_decoder_i
      (
        .instr_rdata_i  ( instr_rdata_i  ),
        .decoder_ctrl_o ( decoder_a_ctrl )
      );
    end else begin: no_a_decoder
      assign decoder_a_ctrl = DECODER_CTRL_ILLEGAL_INSN;
    end

    if (B_EXT != B_NONE) begin: b_decoder
      // RV32B extension decoder
      cv32e40x_b_decoder
      #(
        .B_EXT (B_EXT)
      )
      b_decoder_i
      (
        .instr_rdata_i  ( instr_rdata_i  ),
        .decoder_ctrl_o ( decoder_b_ctrl )
      );
    end else begin: no_b_decoder
      assign decoder_b_ctrl = DECODER_CTRL_ILLEGAL_INSN;
    end

    if (M_EXT != M_NONE) begin: m_decoder
      // RV32M extension decoder
      cv32e40x_m_decoder
        #(
          .M_EXT (M_EXT)
          )
      m_decoder_i
      (
       .instr_rdata_i  ( instr_rdata_i  ),
       .decoder_ctrl_o ( decoder_m_ctrl )
      );
    end else begin: no_m_decoder
      assign decoder_m_ctrl = DECODER_CTRL_ILLEGAL_INSN;
    end

  endgenerate
      
  // Mux control outputs from decoders
  always_comb
  begin
    unique case (1'b1)
      !decoder_m_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_m_ctrl; // M decoder got a match
      !decoder_a_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_a_ctrl; // A decoder got a match
      !decoder_i_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_i_ctrl; // I decoder got a match
      !decoder_b_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_b_ctrl; // B decoder got a match
      default                      : decoder_ctrl_mux_subdec = DECODER_CTRL_ILLEGAL_INSN; // No match from decoders, illegal instruction
    endcase
  end

  // Take illegal compressed instruction into account
  always_comb begin
    if (illegal_c_insn_i) begin
      decoder_ctrl_mux = DECODER_CTRL_ILLEGAL_INSN;
    end
    else begin
      decoder_ctrl_mux = decoder_ctrl_mux_subdec;
    end
  end

  assign alu_en             = decoder_ctrl_mux.alu_en;
  assign alu_bch_o          = decoder_ctrl_mux.alu_bch;
  assign alu_jmp_o          = decoder_ctrl_mux.alu_jmp;
  assign alu_jmpr_o         = decoder_ctrl_mux.alu_jmpr;
  assign alu_operator_o     = decoder_ctrl_mux.alu_operator;                  
  assign alu_op_a_mux_sel_o = decoder_ctrl_mux.alu_op_a_mux_sel;              
  assign alu_op_b_mux_sel_o = decoder_ctrl_mux.alu_op_b_mux_sel;              
  assign op_c_mux_sel_o     = decoder_ctrl_mux.op_c_mux_sel;
  assign imm_a_mux_sel_o    = decoder_ctrl_mux.imm_a_mux_sel;                 
  assign imm_b_mux_sel_o    = decoder_ctrl_mux.imm_b_mux_sel;                 
  assign bch_jmp_mux_sel_o  = decoder_ctrl_mux.bch_jmp_mux_sel;
  assign mul_en             = decoder_ctrl_mux.mul_en;
  assign mul_operator_o     = decoder_ctrl_mux.mul_operator;               
  assign mul_signed_mode_o  = decoder_ctrl_mux.mul_signed_mode;
  assign div_en             = decoder_ctrl_mux.div_en;
  assign div_operator_o     = decoder_ctrl_mux.div_operator;
  assign rf_re_o            = decoder_ctrl_mux.rf_re;                         
  assign rf_we              = decoder_ctrl_mux.rf_we;                           
  assign csr_en             = decoder_ctrl_mux.csr_en;
  assign csr_op_o           = decoder_ctrl_mux.csr_op;
  assign lsu_en             = decoder_ctrl_mux.lsu_en;                        
  assign lsu_we_o           = decoder_ctrl_mux.lsu_we;                       
  assign lsu_size_o         = decoder_ctrl_mux.lsu_size;                     
  assign lsu_sext_o         = decoder_ctrl_mux.lsu_sext;
  assign lsu_atop_o         = decoder_ctrl_mux.lsu_atop;                     
  assign sys_en             = decoder_ctrl_mux.sys_en;
  assign sys_mret_insn_o    = decoder_ctrl_mux.sys_mret_insn;
  assign sys_dret_insn_o    = decoder_ctrl_mux.sys_dret_insn;
  assign sys_ebrk_insn_o    = decoder_ctrl_mux.sys_ebrk_insn;
  assign sys_ecall_insn_o   = decoder_ctrl_mux.sys_ecall_insn;
  assign sys_wfi_insn_o     = decoder_ctrl_mux.sys_wfi_insn;
  assign sys_fencei_insn_o  = decoder_ctrl_mux.sys_fencei_insn;

  // Suppress control signals
  assign alu_en_o = deassert_we_i ? 1'b0        : alu_en;
  assign sys_en_o = deassert_we_i ? 1'b0        : sys_en;
  assign mul_en_o = deassert_we_i ? 1'b0        : mul_en;
  assign div_en_o = deassert_we_i ? 1'b0        : div_en;
  assign lsu_en_o = deassert_we_i ? 1'b0        : lsu_en;

  assign csr_en_o = deassert_we_i ? 1'b0        : csr_en;
  assign rf_we_o  = deassert_we_i ? 1'b0        : rf_we;

  // Suppress special instruction/illegal instruction bits
  assign illegal_insn_o = deassert_we_i ? 1'b0 : decoder_ctrl_mux.illegal_insn;

  assign alu_en_raw_o = alu_en;
  
endmodule // cv32e40x_decoder
