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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_id_stage import cv32e40x_pkg::*;
#(
  parameter USE_PMP                 =  0,
  parameter A_EXTENSION             =  0,
  parameter DEBUG_TRIGGER_EN        =  1
)
(
    input  logic        clk,                    // Gated clock
    input  logic        clk_ungated_i,          // Ungated clock
    input  logic        rst_n,

    input  logic        scan_cg_en_i,

    input  logic        fetch_enable_i,
    output logic        ctrl_busy_o,
    output logic        is_decoding_o,

    // Interface to IF stage
    output logic              instr_req_o,

    // Jumps and branches
    input  logic        branch_decision_i,
    output logic [31:0] jump_target_o,

    // IF and ID stage signals
    output logic        clear_instr_valid_o,
    output logic        pc_set_o,
    output pc_mux_e     pc_mux_o,
    output exc_pc_mux_e exc_pc_mux_o,

    // Stalls
    output logic        halt_if_o,      // controller requests a halt of the IF stage

    output logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction
    input  logic        wb_ready_i,     // WB stage is ready for the next instruction

    output logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done
 
    // IF/ID pipeline
    input if_id_pipe_t if_id_pipe_i,

    // ID/EX pipeline 
    output id_ex_pipe_t id_ex_pipe_o,

    input  PrivLvl_t    current_priv_lvl_i,
    output logic [5:0]  csr_cause_o,
    output logic        csr_save_if_o,
    output logic        csr_save_id_o,
    output logic        csr_save_ex_o,
    output logic        csr_restore_mret_id_o,
    output logic        csr_restore_dret_id_o,
    output logic        csr_save_cause_o,

    input  logic        lsu_misaligned_i,
    input  logic        data_err_i,
    output logic        data_err_ack_o,

    // Interrupt signals
    input  logic [31:0] irq_i,
    input  logic [31:0] mie_bypass_i,           // MIE CSR (bypass)
    output logic [31:0] mip_o,                  // MIP CSR
    input  logic        m_irq_enable_i,
    output logic        irq_ack_o,
    output logic [4:0]  irq_id_o,
    output logic [4:0]  exc_cause_o,

    // Debug Signal
    output logic        debug_mode_o,
    output logic [2:0]  debug_cause_o,
    output logic        debug_csr_save_o,
    input  logic        debug_req_i,
    input  logic        debug_single_step_i,
    input  logic        debug_ebreakm_i,
    input  logic        trigger_match_i,
    output logic        debug_havereset_o,
    output logic        debug_running_o,
    output logic        debug_halted_o,

    // Wakeup Signal
    output logic        wake_from_sleep_o,

    // Register file write back and forwards
    input  logic           rf_we_wb_i,
    input  rf_addr_t       rf_waddr_wb_i,
    input  logic [31:0]    rf_wdata_wb_i,

    input  logic           rf_we_ex_i,
    input  rf_addr_t       rf_waddr_ex_i,
    input  logic [31:0]    rf_wdata_ex_i,

    // Performance Counters
    output logic        mhpmevent_minstret_o,
    output logic        mhpmevent_load_o,
    output logic        mhpmevent_store_o,
    output logic        mhpmevent_jump_o,
    output logic        mhpmevent_branch_o,
    output logic        mhpmevent_branch_taken_o,
    output logic        mhpmevent_compressed_o,
    output logic        mhpmevent_jr_stall_o,
    output logic        mhpmevent_imiss_o,
    output logic        mhpmevent_ld_stall_o,

    input  logic        perf_imiss_i
);

  // Source/Destination register instruction index
  localparam REG_S1_MSB = 19;
  localparam REG_S1_LSB = 15;

  localparam REG_S2_MSB = 24;
  localparam REG_S2_LSB = 20;

  localparam REG_S4_MSB = 31;
  localparam REG_S4_LSB = 27;

  localparam REG_D_MSB  = 11;
  localparam REG_D_LSB  = 7;

  logic [31:0] instr;


  // Decoder/Controller ID stage internal signals
  logic        deassert_we;

  logic        illegal_insn;
  logic        ebrk_insn;
  logic        mret_insn;
  logic        dret_insn;
  logic        ecall_insn;
  logic        wfi_insn;
  logic        fencei_insn;

  logic        branch_taken_ex;
  logic [1:0]  ctrl_transfer_insn;
  logic [1:0]  ctrl_transfer_insn_raw;

  logic        misaligned_stall;
  logic        jr_stall;
  logic        load_stall;
  logic        halt_id;
  logic        halt_if;

  logic        debug_wfi_no_sleep;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;
  logic [31:0] imm_z_type;

  logic [31:0] imm_a;           // contains the immediate for operand b
  logic [31:0] imm_b;           // contains the immediate for operand b

  // Signals running between controller and int_controller
  logic        irq_req_ctrl;
  logic        irq_wu_ctrl;
  logic [4:0]  irq_id_ctrl;

  // Register file read interface
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re;
  rf_addr_t    rf_raddr[REGFILE_NUM_READ_PORTS];
  rf_data_t    regfile_rdata[REGFILE_NUM_READ_PORTS];

  // Register file write interface
  rf_addr_t    regfile_waddr[REGFILE_NUM_WRITE_PORTS];
  rf_data_t    regfile_wdata[REGFILE_NUM_WRITE_PORTS];
  logic        regfile_we   [REGFILE_NUM_WRITE_PORTS];
  
  rf_addr_t    rf_waddr;
  logic        regfile_alu_we_dec;

  // Register Write Control
  logic        rf_we;
  logic        rf_we_raw;
  
  // ALU Control
  logic        alu_en;
  alu_opcode_e alu_operator;
  alu_op_a_mux_e alu_op_a_mux_sel;
  alu_op_b_mux_e alu_op_b_mux_sel;
  alu_op_c_mux_e alu_op_c_mux_sel;

  imm_a_mux_e  imm_a_mux_sel;
  imm_b_mux_e  imm_b_mux_sel;
  jt_mux_e     ctrl_transfer_target_mux_sel;

  // Multiplier Control
  mul_opcode_e mult_operator;    // multiplication operation selection
  logic        mult_en;          // multiplication is used instead of ALU
  logic [1:0]  mult_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers

  // Data Memory Control
  logic        data_we;
  logic [1:0]  data_type;
  logic        data_sign_ext;
  logic [1:0]  data_reg_offset;
  logic        data_req;
  logic        data_req_raw;
  logic [5:0]  data_atop;               // Atomic memory instruction

  // CSR control
  logic        csr_access;
  csr_opcode_e csr_op;
  logic        csr_status;

  logic        prepost_useincr;

  // Forwarding
  op_fw_mux_e  operand_a_fw_mux_sel;
  op_fw_mux_e  operand_b_fw_mux_sel;
  logic [31:0] operand_a_fw;
  logic [31:0] operand_b_fw;

  logic [31:0] operand_b;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] alu_operand_c;

  logic        mret_dec;
  logic        dret_dec;

  // Performance counters
  logic        id_valid_q;
  logic        minstret;

  assign instr = if_id_pipe_i.instr.bus_resp.rdata;

  // immediate extraction and sign extension
  assign imm_i_type  = { {20 {instr[31]}}, instr[31:20] };
  assign imm_s_type  = { {20 {instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_sb_type = { {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type  = { instr[31:12], 12'b0 };
  assign imm_uj_type = { {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign imm_z_type  = { 27'b0, instr[REG_S1_MSB:REG_S1_LSB] };


  //---------------------------------------------------------------------------
  // Source register selection
  //---------------------------------------------------------------------------
  assign rf_raddr[0] = instr[REG_S1_MSB:REG_S1_LSB];
  assign rf_raddr[1] = instr[REG_S2_MSB:REG_S2_LSB];

  //---------------------------------------------------------------------------
  // Destination register seclection
  //---------------------------------------------------------------------------
  assign rf_waddr = instr[REG_D_MSB:REG_D_LSB];

  // kill instruction in the IF/ID stage by setting the instr_valid_id control
  // signal to 0 for instructions that are done
  assign clear_instr_valid_o = id_ready_o | halt_id | branch_taken_ex;

  assign branch_taken_ex = id_ex_pipe_o.branch_in_ex && branch_decision_i;

  //////////////////////////////////////////////////////////////////
  //      _                         _____                    _    //
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_  //
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __| //
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_  //
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__| //
  //                       |_|                    |___/           //
  //////////////////////////////////////////////////////////////////

  always_comb begin : jump_target_mux
    unique case (ctrl_transfer_target_mux_sel)
      JT_JAL:  jump_target_o = if_id_pipe_i.pc + imm_uj_type;
      JT_COND: jump_target_o = if_id_pipe_i.pc + imm_sb_type;
      JT_JALR: jump_target_o = regfile_rdata[0] + imm_i_type;             // JALR: Cannot forward RS1, since the path is too long
      default: jump_target_o = regfile_rdata[0] + imm_i_type;
    endcase
  end


  ////////////////////////////////////////////////////////
  //   ___                                 _      _     //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \    //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \   //
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\ //
  //       |_|                                          //
  ////////////////////////////////////////////////////////

  // ALU_Op_a Mux
  always_comb begin : alu_operand_a_mux
    case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw;
      OP_A_REGB_OR_FWD:  alu_operand_a = operand_b_fw;
      OP_A_CURRPC:       alu_operand_a = if_id_pipe_i.pc;
      OP_A_IMM:          alu_operand_a = imm_a;
      default:           alu_operand_a = operand_a_fw;
    endcase; // case (alu_op_a_mux_sel)
  end

  always_comb begin : immediate_a_mux
    unique case (imm_a_mux_sel)
      IMMA_Z:      imm_a = imm_z_type;
      IMMA_ZERO:   imm_a = '0;
    endcase
  end

  // Operand a forwarding mux
  always_comb begin : operand_a_fw_mux
    case (operand_a_fw_mux_sel)
      SEL_FW_EX:    operand_a_fw = (rf_re[0] || lsu_misaligned_i) ? rf_wdata_ex_i : 32'b0;
      SEL_FW_WB:    operand_a_fw = rf_re[0] ? rf_wdata_wb_i : 32'b0;
      SEL_REGFILE:  operand_a_fw = rf_re[0] ? regfile_rdata[0] : 32'b0;
      default:      operand_a_fw = rf_re[0] ? regfile_rdata[0] : 32'b0;
/* TODO:OK: reintroduce following code when RF write port removal is done
      SEL_FW_EX:    operand_a_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_a_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_a_fw = regfile_rdata[0];
      default:      operand_a_fw = regfile_rdata[0];
*/
    endcase; // case (operand_a_fw_mux_sel)
  end

  //////////////////////////////////////////////////////
  //   ___                                 _   ____   //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| | | __ )  //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | |  _ \  //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |_) | //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| |____/  //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // Immediate Mux for operand B
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      IMMB_I:      imm_b = imm_i_type;
      IMMB_S:      imm_b = imm_s_type;
      IMMB_U:      imm_b = imm_u_type;
      IMMB_PCINCR: imm_b = if_id_pipe_i.is_compressed ? 32'h2 : 32'h4;
      default:     imm_b = imm_i_type;
    endcase
  end

  // ALU_Op_b Mux
  always_comb begin : alu_operand_b_mux
    case (alu_op_b_mux_sel)
      OP_B_REGA_OR_FWD:  operand_b = operand_a_fw;
      OP_B_REGB_OR_FWD:  operand_b = operand_b_fw;
      OP_B_IMM:          operand_b = imm_b;
      default:           operand_b = operand_b_fw;
    endcase // case (alu_op_b_mux_sel)
  end


  // choose normal or scalar replicated version of operand b
  assign alu_operand_b = operand_b;


  // Operand b forwarding mux
  always_comb begin : operand_b_fw_mux
    case (operand_b_fw_mux_sel)
      SEL_FW_EX:    operand_b_fw = rf_re[1] ? rf_wdata_ex_i : 32'b0;
      SEL_FW_WB:    operand_b_fw = rf_re[1] ? rf_wdata_wb_i : 32'b0;
      SEL_REGFILE:  operand_b_fw = rf_re[1] ? regfile_rdata[1] : 32'b0;
      default:      operand_b_fw = rf_re[1] ? regfile_rdata[1] : 32'b0;
/* TODO:OK: reintroduce following code when RF write port removal is done
      SEL_FW_EX:    operand_b_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_b_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_b_fw = regfile_rdata[1];
      default:      operand_b_fw = regfile_rdata[1];
*/
    endcase; // case (operand_b_fw_mux_sel)
  end


  //////////////////////////////////////////////////////
  //   ___                                 _    ____  //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |  / ___| //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | | |     //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |___  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_|  \____| //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // ALU OP C Mux
  always_comb begin : alu_operand_c_mux
    case (alu_op_c_mux_sel)
      OP_C_REGB_OR_FWD:  alu_operand_c = operand_b_fw;
      OP_C_JT:           alu_operand_c = jump_target_o;
      OP_C_FWD:          alu_operand_c = 32'h0;
      default:           alu_operand_c = 32'h0;
    endcase // case (alu_op_c_mux_sel)
  end

  /////////////////////////////////////////////////////////
  //  ____  _____ ____ ___ ____ _____ _____ ____  ____   //
  // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|  //
  // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \  //
  // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) | //
  // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/  //
  //                                                     //
  /////////////////////////////////////////////////////////

  // Connect register file write port(s) to appropriate signals
  assign regfile_we[0]    = rf_we_wb_i;
  assign regfile_waddr[0] = rf_waddr_wb_i;
  assign regfile_wdata[0] = rf_wdata_wb_i;

  assign regfile_we[1]    = rf_we_ex_i && !id_ex_pipe_o.data_req;
  assign regfile_waddr[1] = rf_waddr_ex_i;
  assign regfile_wdata[1] = rf_wdata_ex_i;

  cv32e40x_register_file_wrapper
  register_file_wrapper_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_n              ),

    // Read ports
    .raddr_i            ( rf_raddr           ),
    .rdata_o            ( regfile_rdata      ),

    // Write ports
    .waddr_i            ( regfile_waddr      ),
    .wdata_i            ( regfile_wdata      ),
    .we_i               ( regfile_we         )
               
  );


  ///////////////////////////////////////////////
  //  ____  _____ ____ ___  ____  _____ ____   //
  // |  _ \| ____/ ___/ _ \|  _ \| ____|  _ \  //
  // | | | |  _|| |  | | | | | | |  _| | |_) | //
  // | |_| | |__| |__| |_| | |_| | |___|  _ <  //
  // |____/|_____\____\___/|____/|_____|_| \_\ //
  //                                           //
  ///////////////////////////////////////////////

  cv32e40x_decoder
    #(
      .A_EXTENSION             ( A_EXTENSION            ),
      .USE_PMP                 ( USE_PMP                ),
      .DEBUG_TRIGGER_EN        ( DEBUG_TRIGGER_EN       )
      )
  decoder_i
  (
    // controller related signals
    .deassert_we_i                   ( deassert_we               ),

    .illegal_insn_o                  ( illegal_insn              ),
    .ebrk_insn_o                     ( ebrk_insn                 ),
    .mret_insn_o                     ( mret_insn                 ),
    .dret_insn_o                     ( dret_insn                 ),
    .mret_dec_o                      ( mret_dec                  ),
    .dret_dec_o                      ( dret_dec                  ),
    .ecall_insn_o                    ( ecall_insn                ),
    .wfi_insn_o                      ( wfi_insn                  ),
    .fencei_insn_o                   ( fencei_insn               ),
    
    // from IF/ID pipeline
    .instr_rdata_i                   ( instr                     ),
    .illegal_c_insn_i                ( if_id_pipe_i.illegal_c_insn ),

    // ALU signals
    .alu_en_o                        ( alu_en                    ),
    .alu_operator_o                  ( alu_operator              ),
    .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel          ),
    .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel          ),
    .alu_op_c_mux_sel_o              ( alu_op_c_mux_sel          ),
    .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
    .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),

    // MUL signals
    .mult_en_o                       ( mult_en                   ),
    .mult_operator_o                 ( mult_operator             ),
    .mult_signed_mode_o              ( mult_signed_mode          ),

    // Register file control signals
    .rf_re_o                         ( rf_re                     ),
    .rf_we_o                         ( rf_we                     ),
    .rf_we_raw_o                     ( rf_we_raw                 ),

    // CSR control signals
    .csr_access_o                    ( csr_access                ),
    .csr_status_o                    ( csr_status                ),
    .csr_op_o                        ( csr_op                    ),
    .current_priv_lvl_i              ( current_priv_lvl_i        ),

    // Data bus interface
    .data_req_o                      ( data_req                  ),
    .data_req_raw_o                  ( data_req_raw              ),
    .data_we_o                       ( data_we                   ),
    .prepost_useincr_o               ( prepost_useincr           ),
    .data_type_o                     ( data_type                 ),
    .data_sign_ext_o                 ( data_sign_ext             ),
    .data_reg_offset_o               ( data_reg_offset           ),
    .data_atop_o                     ( data_atop                 ),

    // debug mode
    .debug_mode_i                    ( debug_mode_o              ),
    .debug_wfi_no_sleep_i            ( debug_wfi_no_sleep        ),

    // jump/branches
    .ctrl_transfer_insn_o            ( ctrl_transfer_insn        ),
    .ctrl_transfer_insn_raw_o        ( ctrl_transfer_insn_raw    ),
    .ctrl_transfer_target_mux_sel_o  ( ctrl_transfer_target_mux_sel )
  );

  assign regfile_alu_we_dec = rf_we_raw && !data_req_raw;


  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////

  cv32e40x_controller
  controller_i
  (
    .clk                            ( clk                    ),         // Gated clock
    .clk_ungated_i                  ( clk_ungated_i          ),         // Ungated clock
    .rst_n                          ( rst_n                  ),

    .fetch_enable_i                 ( fetch_enable_i         ),
    .ctrl_busy_o                    ( ctrl_busy_o            ),
    .is_decoding_o                  ( is_decoding_o          ),

    // decoder related signals
    .deassert_we_o                  ( deassert_we            ),

    .illegal_insn_i                 ( illegal_insn           ),
    .ecall_insn_i                   ( ecall_insn             ),
    .mret_insn_i                    ( mret_insn              ),
    .dret_insn_i                    ( dret_insn              ),
    .mret_dec_i                     ( mret_dec               ),
    .dret_dec_i                     ( dret_dec               ),
    .wfi_insn_i                     ( wfi_insn               ),
    .ebrk_insn_i                    ( ebrk_insn              ),
    .fencei_insn_i                  ( fencei_insn            ),

    .csr_status_i                   ( csr_status             ),

    // from IF/ID pipeline
    .if_id_pipe_i                   (if_id_pipe_i            ),
    // from prefetcher
    .instr_req_o                    ( instr_req_o                ),
                                                                 
    // to prefetcher                                             
    .pc_set_o                       ( pc_set_o                   ),
    .pc_mux_o                       ( pc_mux_o                   ),
    .exc_pc_mux_o                   ( exc_pc_mux_o               ),
    .exc_cause_o                    ( exc_cause_o                ),

    // LSU
    .data_req_ex_i                  ( id_ex_pipe_o.data_req  ),
    .data_we_ex_i                   ( id_ex_pipe_o.data_we   ),
    .data_misaligned_i              ( lsu_misaligned_i       ),

    // jump/branch control
    .branch_taken_ex_i              ( branch_taken_ex        ),
    .ctrl_transfer_insn_i           ( ctrl_transfer_insn     ),
    .ctrl_transfer_insn_raw_i       ( ctrl_transfer_insn_raw ),

    // Interrupt signals
    .irq_wu_ctrl_i                  ( irq_wu_ctrl            ),
    .irq_req_ctrl_i                 ( irq_req_ctrl           ),
    .irq_id_ctrl_i                  ( irq_id_ctrl            ),
    .current_priv_lvl_i             ( current_priv_lvl_i     ),
    .irq_ack_o                      ( irq_ack_o              ),
    .irq_id_o                       ( irq_id_o               ),

    // Debug Signal
    .debug_mode_o                   ( debug_mode_o           ),
    .debug_cause_o                  ( debug_cause_o          ),
    .debug_csr_save_o               ( debug_csr_save_o       ),
    .debug_req_i                    ( debug_req_i            ),
    .debug_single_step_i            ( debug_single_step_i    ),
    .debug_ebreakm_i                ( debug_ebreakm_i        ),
    .trigger_match_i                ( trigger_match_i        ),
    .debug_wfi_no_sleep_o           ( debug_wfi_no_sleep     ),
    .debug_havereset_o              ( debug_havereset_o      ),
    .debug_running_o                ( debug_running_o        ),
    .debug_halted_o                 ( debug_halted_o         ),

    // Wakeup Signal
    .wake_from_sleep_o              ( wake_from_sleep_o      ),

    // CSR Controller Signals
    .csr_save_cause_o               ( csr_save_cause_o       ),
    .csr_cause_o                    ( csr_cause_o            ),
    .csr_save_if_o                  ( csr_save_if_o          ),
    .csr_save_id_o                  ( csr_save_id_o          ),
    .csr_save_ex_o                  ( csr_save_ex_o          ),
    .csr_restore_mret_id_o          ( csr_restore_mret_id_o  ),
    .csr_restore_dret_id_o          ( csr_restore_dret_id_o  ),

    // Register File read, write back and forwards
    .rf_re_i                        ( rf_re                  ),       
    .rf_raddr_i                     ( rf_raddr               ),
    .rf_waddr_i                     ( rf_waddr               ),
    .rf_we_ex_i                     ( rf_we_ex_i             ),
    .rf_waddr_ex_i                  ( rf_waddr_ex_i          ),
    .rf_we_wb_i                     ( rf_we_wb_i             ),
    .rf_waddr_wb_i                  ( rf_waddr_wb_i          ),

    // Write targets from ID
    .regfile_alu_we_id_i            ( regfile_alu_we_dec    ),
   
    // Forwarding signals
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel   ),

    // Stall signals
    .halt_if_o                      ( halt_if                ),
    .halt_id_o                      ( halt_id                ),

    .misaligned_stall_o             ( misaligned_stall       ),
    .jr_stall_o                     ( jr_stall               ),
    .load_stall_o                   ( load_stall             ),

    .id_ready_i                     ( id_ready_o             ),
    .id_valid_i                     ( id_valid_o             ),
    .ex_valid_i                     ( ex_valid_i             ),
    .wb_ready_i                     ( wb_ready_i             )
  );


////////////////////////////////////////////////////////////////////////
//  _____      _       _____             _             _ _            //
// |_   _|    | |     /  __ \           | |           | | |           //
//   | | _ __ | |_    | /  \/ ___  _ __ | |_ _ __ ___ | | | ___ _ __  //
//   | || '_ \| __|   | |    / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__| //
//  _| || | | | |_ _  | \__/\ (_) | | | | |_| | | (_) | | |  __/ |    //
//  \___/_| |_|\__(_)  \____/\___/|_| |_|\__|_|  \___/|_|_|\___|_|    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

  cv32e40x_int_controller
  int_controller_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_n              ),

    // External interrupt lines
    .irq_i                ( irq_i              ),

    // To cv32e40x_controller
    .irq_req_ctrl_o       ( irq_req_ctrl       ),
    .irq_id_ctrl_o        ( irq_id_ctrl        ),
    .irq_wu_ctrl_o        ( irq_wu_ctrl        ),

    // To/from with cv32e40x_cs_registers
    .mie_bypass_i         ( mie_bypass_i       ),
    .mip_o                ( mip_o              ),
    .m_ie_i               ( m_irq_enable_i     ),
    .current_priv_lvl_i   ( current_priv_lvl_i )
  );

  
  /////////////////////////////////////////////////////////////////////////////////
  //   ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____   //
  //  |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|  //
  //   | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|    //
  //   | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___   //
  //  |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|  //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      id_ex_pipe_o.alu_en                 <= '0;
      id_ex_pipe_o.alu_operator           <= ALU_SLTU;
      id_ex_pipe_o.alu_operand_a          <= '0;
      id_ex_pipe_o.alu_operand_b          <= '0;
      id_ex_pipe_o.alu_operand_c          <= '0;

      id_ex_pipe_o.mult_en                <= 1'b0;
      id_ex_pipe_o.mult_operator          <= MUL_M32;
      id_ex_pipe_o.mult_operand_a         <= '0;
      id_ex_pipe_o.mult_operand_b         <= '0;
      id_ex_pipe_o.mult_signed_mode       <= 2'b00;

      id_ex_pipe_o.rf_we                  <= 1'b0;
      id_ex_pipe_o.rf_waddr               <= '0;

      id_ex_pipe_o.prepost_useincr        <= 1'b0;

      id_ex_pipe_o.csr_access             <= 1'b0;
      id_ex_pipe_o.csr_op                 <= CSR_OP_READ;

      id_ex_pipe_o.data_req               <= 1'b0;
      id_ex_pipe_o.data_we                <= 1'b0;
      id_ex_pipe_o.data_type              <= 2'b0;
      id_ex_pipe_o.data_sign_ext          <= 1'b0;
      id_ex_pipe_o.data_reg_offset        <= 2'b0;
      id_ex_pipe_o.data_misaligned        <= 1'b0;
      id_ex_pipe_o.data_atop              <= 5'b0;

      id_ex_pipe_o.pc                     <= '0;

      id_ex_pipe_o.branch_in_ex           <= 1'b0;

    end
    else if (lsu_misaligned_i) begin
      // misaligned data access case
      if (ex_ready_i)
      begin // misaligned access case, only unstall alu operands

        // if we are using post increments, then we have to use the
        // original value of the register for the second memory access
        // => keep it stalled
        if (id_ex_pipe_o.prepost_useincr == 1'b1)
        begin
          id_ex_pipe_o.alu_operand_a        <= operand_a_fw;
        end

        id_ex_pipe_o.alu_operand_b          <= 32'h4;
        id_ex_pipe_o.prepost_useincr        <= 1'b1;
        id_ex_pipe_o.data_misaligned        <= 1'b1;
      end
    end
    else begin
      // normal pipeline unstall case

      if (id_valid_o)
      begin // unstall the whole pipeline
        id_ex_pipe_o.alu_en                 <= alu_en;
        if (alu_en)
        begin
          id_ex_pipe_o.alu_operator         <= alu_operator;
          id_ex_pipe_o.alu_operand_a        <= alu_operand_a;
          id_ex_pipe_o.alu_operand_b        <= alu_operand_b;
          id_ex_pipe_o.alu_operand_c        <= alu_operand_c;
        end

        id_ex_pipe_o.mult_en                <= mult_en;
        if (mult_en) begin
          id_ex_pipe_o.mult_operator        <= mult_operator;
          id_ex_pipe_o.mult_signed_mode     <= mult_signed_mode;
          id_ex_pipe_o.mult_operand_a       <= alu_operand_a;
          id_ex_pipe_o.mult_operand_b       <= alu_operand_b;
        end
        
        id_ex_pipe_o.rf_we                  <= rf_we;
        if (rf_we) begin
          id_ex_pipe_o.rf_waddr             <= rf_waddr;
        end

        id_ex_pipe_o.prepost_useincr        <= prepost_useincr;

        id_ex_pipe_o.csr_access             <= csr_access;
        id_ex_pipe_o.csr_op                 <= csr_op;

        id_ex_pipe_o.data_req               <= data_req;
        if (data_req)
        begin // only needed for LSU when there is an active request
          id_ex_pipe_o.data_we              <= data_we;
          id_ex_pipe_o.data_type            <= data_type;
          id_ex_pipe_o.data_sign_ext        <= data_sign_ext;
          id_ex_pipe_o.data_reg_offset      <= data_reg_offset;
          id_ex_pipe_o.data_atop            <= data_atop;
        end

        id_ex_pipe_o.data_misaligned        <= 1'b0;

        if ((ctrl_transfer_insn == BRANCH_COND) || data_req) begin
          id_ex_pipe_o.pc                   <= if_id_pipe_i.pc;
        end

        id_ex_pipe_o.branch_in_ex           <= ctrl_transfer_insn == BRANCH_COND;
      end else if (ex_ready_i) begin
        // EX stage is ready but we don't have a new instruction for it,
        // so we set all write enables to 0, but unstall the pipe

        id_ex_pipe_o.rf_we                  <= 1'b0;

        id_ex_pipe_o.csr_op                 <= CSR_OP_READ;

        id_ex_pipe_o.data_req               <= 1'b0;
        id_ex_pipe_o.data_misaligned        <= 1'b0;

        id_ex_pipe_o.branch_in_ex           <= 1'b0;

        id_ex_pipe_o.alu_en                 <= 1'b1;            // todo: requires explanation
        id_ex_pipe_o.alu_operator           <= ALU_SLTU;        // todo: requires explanation

        id_ex_pipe_o.mult_en                <= 1'b0;

      end else if (id_ex_pipe_o.csr_access) begin
       //In the EX stage there was a CSR access, to avoid multiple
       //writes to the RF, disable rf_we.
       //Not doing it can overwrite the RF file with the currennt CSR value rather than the old one
       id_ex_pipe_o.rf_we         <= 1'b0;
      end
    end
  end

  // Performance Counter Events

  // Illegal/ebreak/ecall are never counted as retired instructions. Note that actually issued instructions
  // are being counted; the manner in which CSR instructions access the performance counters guarantees
  // that this count will correspond to the retired isntructions count.
  assign minstret = id_valid_o && is_decoding_o && !(illegal_insn || ebrk_insn || ecall_insn);

  always_ff @(posedge clk , negedge rst_n)
  begin
    if ( rst_n == 1'b0 )
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
      // Helper signal
      id_valid_q                 <= id_valid_o;
      // ID stage counts
      mhpmevent_minstret_o       <= minstret;
      mhpmevent_load_o           <= minstret && data_req && !data_we;
      mhpmevent_store_o          <= minstret && data_req && data_we;
      mhpmevent_jump_o           <= minstret && ((ctrl_transfer_insn == BRANCH_JAL) || (ctrl_transfer_insn == BRANCH_JALR));
      mhpmevent_branch_o         <= minstret && (ctrl_transfer_insn == BRANCH_COND);
      mhpmevent_compressed_o     <= minstret && if_id_pipe_i.is_compressed;
      // EX stage count
      mhpmevent_branch_taken_o   <= mhpmevent_branch_o && branch_decision_i;
      // IF stage count
      mhpmevent_imiss_o          <= perf_imiss_i;
      // Jump-register-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_jr_stall_o       <= jr_stall && !halt_id && id_valid_q;
      // Load-use-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_ld_stall_o       <= load_stall && !halt_id && id_valid_q;
    end
  end

  // stall control
  assign id_ready_o = ((~misaligned_stall) & (~jr_stall) & (~load_stall) & ex_ready_i);
  assign id_valid_o = (~halt_id) & id_ready_o;
  assign halt_if_o  = halt_if;

endmodule // cv32e40x_id_stage
