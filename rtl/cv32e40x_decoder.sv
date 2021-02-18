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
  parameter A_EXTENSION       = 0,
  parameter USE_PMP           = 0,
  parameter DEBUG_TRIGGER_EN  = 1
)
(
  // singals running to/from controller
  input  logic        deassert_we_i,           // deassert we, we are stalled or not active

  output logic        illegal_insn_o,          // illegal instruction encountered
  output logic        ebrk_insn_o,             // trap instruction encountered

  output logic        mret_insn_o,             // return from exception instruction encountered (M)
  output logic        dret_insn_o,             // return from debug (M)

  output logic        mret_dec_o,              // return from exception instruction encountered (M) without deassert
  output logic        dret_dec_o,              // return from debug (M) without deassert

  output logic        ecall_insn_o,            // environment call (syscall) instruction encountered
  output logic        wfi_insn_o,              // pipeline flush is requested

  output logic        fencei_insn_o,           // fence.i instruction

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,           // instruction read from instr memory/cache
  input  logic        illegal_c_insn_i,        // compressed instruction decode failed

  // ALU signals
  output logic        alu_en_o,                // ALU enable
  output alu_opcode_e alu_operator_o, // ALU operation selection
  output alu_op_a_mux_e alu_op_a_mux_sel_o,      // operand a selection: reg value, PC, immediate or zero
  output alu_op_b_mux_e alu_op_b_mux_sel_o,      // operand b selection: reg value or immediate
  output alu_op_c_mux_e alu_op_c_mux_sel_o,      // operand c selection: reg value or jump target
  output imm_a_mux_e    imm_a_mux_sel_o,         // immediate selection for operand a
  output imm_b_mux_e    imm_b_mux_sel_o,         // immediate selection for operand b

  // MUL related control signals
  output mul_opcode_e mult_operator_o,         // Multiplication operation selection
  output logic        mult_en_o,               // Perform integer multiplication
  output logic        mult_sel_subword_o,      // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,      // Multiplication in signed mode
  
  // Register file related signals
  output logic        rf_we_o,                 // Write enable for register file
  output logic        rf_we_raw_o,             // Write enable for register file without deassert
  output logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_o,

  // CSR manipulation
  output logic        csr_access_o,            // access to CSR
  output logic        csr_status_o,            // access to xstatus CSR
  output csr_opcode_e csr_op_o,                // operation to perform on CSR
  input  PrivLvl_t    current_priv_lvl_i,      // The current privilege level

  // LD/ST unit signals
  output logic        data_req_o,              // start transaction to data memory
  output logic        data_req_raw_o,
  output logic        data_we_o,               // data memory write enable
  output logic        prepost_useincr_o,       // when not active bypass the alu result for address calculation
  output logic [1:0]  data_type_o,             // data type on data memory: byte, half word or word
  output logic        data_sign_ext_o,         // sign extension on read data from data memory
  output logic [1:0]  data_reg_offset_o,       // offset in byte inside register for stores
  output logic [5:0]  data_atop_o,             // Atomic memory access

  input  logic        debug_mode_i,            // processor is in debug mode
  input  logic        debug_wfi_no_sleep_i,    // do not let WFI cause sleep

  // jump/branches
  output logic [1:0]  ctrl_transfer_insn_o,      // control transfer instructio is decoded
  output logic [1:0]  ctrl_transfer_insn_raw_o,  // control transfer instruction without deassert
  output jt_mux_e     ctrl_transfer_target_mux_sel_o        // jump target selection

);

  // write enable/request control
  logic       rf_we;
  logic       data_req;
  logic       csr_illegal;
  logic [1:0] ctrl_transfer_insn;

  csr_opcode_e csr_op;

  logic       alu_en;
  logic       mult_en;

  decoder_ctrl_t decoder_i_ctrl;
  decoder_ctrl_t decoder_m_ctrl;
  decoder_ctrl_t decoder_a_ctrl;
  decoder_ctrl_t decoder_ctrl_mux_subdec;
  decoder_ctrl_t decoder_ctrl_mux;

  // RV32I Base instruction set decoder
  cv32e40x_i_decoder #(.DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN))
    i_decoder_i
      (.instr_rdata_i(instr_rdata_i),
       .debug_mode_i(debug_mode_i),
       .debug_wfi_no_sleep_i(debug_wfi_no_sleep_i),
       .decoder_ctrl_o(decoder_i_ctrl));
  
  // RV32M extension decoder
  cv32e40x_m_decoder
    m_decoder_i
      (.instr_rdata_i(instr_rdata_i),
       .decoder_ctrl_o(decoder_m_ctrl));

  generate
    if (A_EXTENSION) begin: a_decoder
      // RV32A extension decoder
      cv32e40x_a_decoder
        a_decoder_i
          (.instr_rdata_i(instr_rdata_i),
           .decoder_ctrl_o(decoder_a_ctrl));
    end
    else begin: no_a_decoder
      assign decoder_a_ctrl = DECODER_CTRL_ILLEGAL_INSN;
    end
  endgenerate
      
  // Mux control outputs from decoders
  always_comb
  begin
    unique case (1'b1)
      !decoder_m_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_m_ctrl; // M decoder got a match
      !decoder_a_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_a_ctrl; // A decoder got a match
      !decoder_i_ctrl.illegal_insn : decoder_ctrl_mux_subdec = decoder_i_ctrl; // I decoder got a match
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

  assign ctrl_transfer_insn             = decoder_ctrl_mux.ctrl_transfer_insn;
  assign ctrl_transfer_target_mux_sel_o = decoder_ctrl_mux.ctrl_transfer_target_mux_sel;
  assign alu_en                         = decoder_ctrl_mux.alu_en;
  assign alu_operator_o                 = decoder_ctrl_mux.alu_operator;                  
  assign alu_op_a_mux_sel_o             = decoder_ctrl_mux.alu_op_a_mux_sel;              
  assign alu_op_b_mux_sel_o             = decoder_ctrl_mux.alu_op_b_mux_sel;              
  assign alu_op_c_mux_sel_o             = decoder_ctrl_mux.alu_op_c_mux_sel;               
  assign imm_a_mux_sel_o                = decoder_ctrl_mux.imm_a_mux_sel;                 
  assign imm_b_mux_sel_o                = decoder_ctrl_mux.imm_b_mux_sel;                 
  assign mult_operator_o                = decoder_ctrl_mux.mult_operator;                 
  assign mult_en                        = decoder_ctrl_mux.mult_en;                         
  assign mult_signed_mode_o             = decoder_ctrl_mux.mult_signed_mode;              
  assign mult_sel_subword_o             = decoder_ctrl_mux.mult_sel_subword;              
  assign rf_re_o                        = decoder_ctrl_mux.rf_re;                         
  assign rf_we                          = decoder_ctrl_mux.rf_we;                           
  assign prepost_useincr_o              = decoder_ctrl_mux.prepost_useincr;               
  assign csr_access_o                   = decoder_ctrl_mux.csr_access;                    
  assign csr_status_o                   = decoder_ctrl_mux.csr_status;                    
  assign csr_illegal                    = decoder_ctrl_mux.csr_illegal;                     
  assign csr_op                         = decoder_ctrl_mux.csr_op;                          
  assign mret_insn_o                    = decoder_ctrl_mux.mret_insn;                     
  assign dret_insn_o                    = decoder_ctrl_mux.dret_insn;                     
  assign data_req                       = decoder_ctrl_mux.data_req;                        
  assign data_we_o                      = decoder_ctrl_mux.data_we;                       
  assign data_type_o                    = decoder_ctrl_mux.data_type;                     
  assign data_sign_ext_o                = decoder_ctrl_mux.data_sign_ext;
  assign data_reg_offset_o              = decoder_ctrl_mux.data_reg_offset;               
  assign data_atop_o                    = decoder_ctrl_mux.data_atop;                     
  assign illegal_insn_o                 = decoder_ctrl_mux.illegal_insn;        
  assign ebrk_insn_o                    = decoder_ctrl_mux.ebrk_insn;                     
  assign ecall_insn_o                   = decoder_ctrl_mux.ecall_insn;                    
  assign wfi_insn_o                     = decoder_ctrl_mux.wfi_insn;                      
  assign fencei_insn_o                  = decoder_ctrl_mux.fencei_insn;                   
  assign mret_dec_o                     = decoder_ctrl_mux.mret_dec;                      
  assign dret_dec_o                     = decoder_ctrl_mux.dret_dec;                      


  assign alu_en_o             = deassert_we_i ? 1'b0        : alu_en;
  assign mult_en_o            = deassert_we_i ? 1'b0        : mult_en;
  assign rf_we_o              = deassert_we_i ? 1'b0        : rf_we;
  assign data_req_o           = deassert_we_i ? 1'b0        : data_req;
  assign csr_op_o             = deassert_we_i ? CSR_OP_READ : csr_op;
  assign ctrl_transfer_insn_o = deassert_we_i ? BRANCH_NONE : ctrl_transfer_insn;

  assign ctrl_transfer_insn_raw_o = ctrl_transfer_insn;
  assign rf_we_raw_o              = rf_we;
  assign data_req_raw_o           = data_req;

  
endmodule // cv32e40x_decoder
