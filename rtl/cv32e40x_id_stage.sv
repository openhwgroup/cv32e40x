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
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
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
  parameter A_EXTENSION             =  0,
  parameter b_ext_e B_EXT           =  NONE,
  parameter DEBUG_TRIGGER_EN        =  1
)
(
  input  logic        clk,                    // Gated clock
  input  logic        clk_ungated_i,          // Ungated clock
  input  logic        rst_n,

  // Jumps and branches
  output logic [31:0] jmp_target_o,

  // IF/ID pipeline
  input  if_id_pipe_t if_id_pipe_i,

  // ID/EX pipeline 
  output id_ex_pipe_t id_ex_pipe_o,

  // EX/WB pipeline
  input  ex_wb_pipe_t ex_wb_pipe_i,

  // Controller
  input  ctrl_byp_t   ctrl_byp_i,
  input  ctrl_fsm_t   ctrl_fsm_i,

  input  privlvl_t    current_priv_lvl_i,

  // Debug Signal
  input  logic        debug_trigger_match_id_i,

  // Register file write data from WB stage
  input  logic [31:0]    rf_wdata_wb_i,

  // Register file write data from EX stage
  input  logic [31:0]    rf_wdata_ex_i,

  output logic        mret_insn_o,
  output logic        dret_insn_o,
  // Decoder to controller
  output logic        csr_en_o,
  output csr_opcode_e csr_op_o,

  output logic [1:0]  ctrl_transfer_insn_o,
  output logic [1:0]  ctrl_transfer_insn_raw_o,

  // RF interface -> controller
  output logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_o,
  output rf_addr_t    rf_raddr_o[REGFILE_NUM_READ_PORTS],
  output rf_addr_t    rf_waddr_o,

  output logic        regfile_alu_we_id_o,

  // Register file
  input  rf_data_t    regfile_rdata_i[REGFILE_NUM_READ_PORTS],

  // Stage ready/valid
  output logic        id_ready_o,     // ID stage is ready for new data
  output logic        id_valid_o,     // ID stage has valid (non-bubble) data for next stage
  input  logic        ex_ready_i,     // EX stage is ready for new data

  // eXtension interface
  if_xif.cpu_issue  xif_issue_if
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

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;
  logic [31:0] imm_z_type;

  logic [31:0] imm_a;           // contains the immediate for operand b
  logic [31:0] imm_b;           // contains the immediate for operand b

  // Register Read/Write Control
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re;
  logic        rf_we;
  logic        rf_we_raw;
  
  // ALU Control
  logic        alu_en;
  alu_opcode_e alu_operator;
  alu_op_a_mux_e alu_op_a_mux_sel;
  alu_op_b_mux_e alu_op_b_mux_sel;

  op_c_mux_e     op_c_mux_sel;

  imm_a_mux_e  imm_a_mux_sel;
  imm_b_mux_e  imm_b_mux_sel;
  jt_mux_e     ctrl_transfer_target_mux_sel;

  // Multiplier Control
  mul_opcode_e mul_operator;    // multiplication operation selection
  logic        mul_en;          // multiplication is used instead of ALU
  logic [1:0]  mul_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers

  // Divider control
  logic         div_en;
  div_opcode_e  div_operator;
  
  // LSU
  logic        lsu_en;
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic [1:0]  lsu_reg_offset;
  logic        lsu_en_raw;
  logic [5:0]  lsu_atop;                // Atomic memory instruction
  logic        lsu_prepost_useincr;

  // CSR
  logic        csr_en;
  csr_opcode_e csr_op;

  logic [31:0] operand_a_fw;
  logic [31:0] operand_b_fw;

  logic [31:0] jalr_fw;

  logic [31:0] operand_a;
  logic [31:0] operand_b;
  logic [31:0] operand_c;

  // Branch target address
  logic [31:0] bch_target;

  // Stall for multicycle ID instructions
  logic multi_cycle_id_stall;

  // Special insn to travel down pipeline structs
  logic        illegal_insn;
  logic        ecall_insn;
  logic        mret_insn;
  logic        dret_insn;
  logic        wfi_insn;
  logic        ebrk_insn;
  logic        fencei_insn;
  logic        xif_insn_accept;
  logic        xif_insn_reject;

  // Local instruction valid qualifier
  logic        instr_valid;

  // eXtension interface signals
  logic        xif_waiting;

  assign instr_valid = if_id_pipe_i.instr_valid && !ctrl_fsm_i.kill_id && !ctrl_fsm_i.halt_id;

  assign mret_insn_o = mret_insn;
  assign dret_insn_o = dret_insn;

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
  assign rf_raddr_o[0] = instr[REG_S1_MSB:REG_S1_LSB];
  assign rf_raddr_o[1] = instr[REG_S2_MSB:REG_S2_LSB];

  //---------------------------------------------------------------------------
  // Destination register seclection
  //---------------------------------------------------------------------------
  assign rf_waddr_o = instr[REG_D_MSB:REG_D_LSB];

  //////////////////////////////////////////////////////////////////
  //      _                         _____                    _    //
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_  //
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __| //
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_  //
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__| //
  //                       |_|                    |___/           //
  //////////////////////////////////////////////////////////////////

  cv32e40x_pc_target cv32e40x_pc_target_i
  (
    .ctrl_transfer_target_mux_sel_i ( ctrl_transfer_target_mux_sel),
    .pc_id_i                        ( if_id_pipe_i.pc             ),
    .imm_uj_type_i                  ( imm_uj_type                 ),
    .imm_sb_type_i                  ( imm_sb_type                 ),
    .imm_i_type_i                   ( imm_i_type                  ),
    .jalr_fw_i                      ( jalr_fw                     ),
    .bch_target_o                   ( bch_target                  ),
    .jmp_target_o                   ( jmp_target_o                )
               
  );

  ////////////////////////////////////////////////////////
  //   ___                                 _      _     //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \    //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \   //
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\ //
  //       |_|                                          //
  ////////////////////////////////////////////////////////

  // Operand A Mux
  always_comb begin : operand_a_mux
    case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD:  operand_a = operand_a_fw;
      OP_A_CURRPC:       operand_a = if_id_pipe_i.pc;
      OP_A_IMM:          operand_a = imm_a;
      default:           operand_a = operand_a_fw;
    endcase; // case (alu_op_a_mux_sel)
  end

  always_comb begin : immediate_a_mux
    unique case (imm_a_mux_sel)
      IMMA_Z:      imm_a = imm_z_type;
      IMMA_ZERO:   imm_a = '0;
    endcase
  end

  // Operand A forwarding mux
  always_comb begin : operand_a_fw_mux
    case (ctrl_byp_i.operand_a_fw_mux_sel)
      SEL_FW_EX:    operand_a_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_a_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_a_fw = regfile_rdata_i[0];
      default:      operand_a_fw = regfile_rdata_i[0];
    endcase;
  end

  always_comb begin: jalr_fw_mux
    case (ctrl_byp_i.jalr_fw_mux_sel)
      SELJ_FW_WB:   jalr_fw = ex_wb_pipe_i.rf_wdata;
      SELJ_REGFILE: jalr_fw = regfile_rdata_i[0];
      default:      jalr_fw = regfile_rdata_i[0];
    endcase
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
      IMMB_PCINCR: imm_b = if_id_pipe_i.instr_meta.compressed ? 32'h2 : 32'h4;
      default:     imm_b = imm_i_type;
    endcase
  end

  // Operand B Mux
  always_comb begin : operand_b_mux
    case (alu_op_b_mux_sel)
      OP_B_REGB_OR_FWD:  operand_b = operand_b_fw;
      OP_B_IMM:          operand_b = imm_b;
      default:           operand_b = operand_b_fw;
    endcase // case (alu_op_b_mux_sel)
  end

  // Operand B forwarding mux
  always_comb begin : operand_b_fw_mux
    case (ctrl_byp_i.operand_b_fw_mux_sel)
      SEL_FW_EX:    operand_b_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_b_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_b_fw = regfile_rdata_i[1];
      default:      operand_b_fw = regfile_rdata_i[1];
    endcase;
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
  always_comb begin : operand_c_mux
    case (op_c_mux_sel)
      OP_C_REGB_OR_FWD:  operand_c = operand_b_fw;
      OP_C_BCH:          operand_c = bch_target;
      OP_C_FWD:          operand_c = 32'h0;
      default:           operand_c = 32'h0;
    endcase // case (op_c_mux_sel)
  end


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
    .A_EXTENSION                     ( A_EXTENSION               ),
    .B_EXT                           ( B_EXT                     ),
    .DEBUG_TRIGGER_EN                ( DEBUG_TRIGGER_EN          )
  )
  decoder_i
  (
    // controller related signals
    .deassert_we_i                   ( ctrl_byp_i.deassert_we ),

    .illegal_insn_o                  ( illegal_insn              ),
    .ebrk_insn_o                     ( ebrk_insn                 ),
    .mret_insn_o                     ( mret_insn                 ),
    .dret_insn_o                     ( dret_insn                 ),
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
    .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
    .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),

    .op_c_mux_sel_o                  ( op_c_mux_sel              ),

    // MUL signals
    .mul_en_o                        ( mul_en                    ),
    .mul_operator_o                  ( mul_operator              ),
    .mul_signed_mode_o               ( mul_signed_mode           ),

    // DIV signals
    .div_en_o                        ( div_en                    ),
    .div_operator_o                  ( div_operator              ),

    // Register file control signals
    .rf_re_o                         ( rf_re                     ),
    .rf_we_o                         ( rf_we                     ),
    .rf_we_raw_o                     ( rf_we_raw                 ),

    // CSR interface
    .csr_en_o                        ( csr_en                    ),
    .csr_op_o                        ( csr_op                    ),
    .current_priv_lvl_i              ( current_priv_lvl_i        ),

    // LSU interface
    .lsu_en_o                        ( lsu_en                    ),
    .lsu_en_raw_o                    ( lsu_en_raw                ),
    .lsu_we_o                        ( lsu_we                    ),
    .lsu_prepost_useincr_o           ( lsu_prepost_useincr       ),
    .lsu_type_o                      ( lsu_type                  ),
    .lsu_sign_ext_o                  ( lsu_sign_ext              ),
    .lsu_reg_offset_o                ( lsu_reg_offset            ),
    .lsu_atop_o                      ( lsu_atop                  ),

    // From controller fsm
    .ctrl_fsm_i                      ( ctrl_fsm_i                ),

    // jump/branches
    .ctrl_transfer_insn_o            ( ctrl_transfer_insn_o      ),
    .ctrl_transfer_insn_raw_o        ( ctrl_transfer_insn_raw_o  ),
    .ctrl_transfer_target_mux_sel_o  ( ctrl_transfer_target_mux_sel )
  );

  // Speculatively read all source registers for illegal instr, might be required by coprocessor
  assign rf_re_o             = illegal_insn ? '1 : rf_re;

  assign regfile_alu_we_id_o = rf_we_raw && !lsu_en_raw;

  
  /////////////////////////////////////////////////////////////////////////////////
  //   ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____   //
  //  |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|  //
  //   | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|    //
  //   | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___   //
  //  |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|  //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////

  // Populate instruction meta data
  instr_meta_t instr_meta_n;
  always_comb begin
    instr_meta_n        = if_id_pipe_i.instr_meta;
    instr_meta_n.jump  = (ctrl_transfer_insn_o == BRANCH_JAL) ||
                         (ctrl_transfer_insn_o == BRANCH_JALR);
    instr_meta_n.branch = ctrl_transfer_insn_o == BRANCH_COND;
  end

  always_ff @(posedge clk, negedge rst_n)
  begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      id_ex_pipe_o.instr_valid            <= 1'b0;
      id_ex_pipe_o.alu_en                 <= '0;
      id_ex_pipe_o.alu_operator           <= ALU_SLTU;
      id_ex_pipe_o.alu_operand_a          <= 32'b0; // todo: path from data_rdata_i through WB to id_ex_pipe_o_reg_alu_operand_a seems longer than needed (too many gates in ID)
      id_ex_pipe_o.alu_operand_b          <= 32'b0;

      id_ex_pipe_o.operand_c              <= 32'b0;

      id_ex_pipe_o.mul_en                 <= 1'b0;
      id_ex_pipe_o.mul_operator           <= MUL_M32;
      id_ex_pipe_o.mul_operand_a          <= 32'b0;
      id_ex_pipe_o.mul_operand_b          <= 32'b0;
      id_ex_pipe_o.mul_signed_mode        <= 2'b0;

      id_ex_pipe_o.div_en                 <= 1'b0;
      id_ex_pipe_o.div_operator           <= DIV_DIVU;

      id_ex_pipe_o.rf_we                  <= 1'b0;
      id_ex_pipe_o.rf_waddr               <= '0;

      id_ex_pipe_o.csr_en                 <= 1'b0;
      id_ex_pipe_o.csr_op                 <= CSR_OP_READ;

      id_ex_pipe_o.lsu_en                 <= 1'b0;
      id_ex_pipe_o.lsu_we                 <= 1'b0;
      id_ex_pipe_o.lsu_type               <= 2'b0;
      id_ex_pipe_o.lsu_sign_ext           <= 1'b0;
      id_ex_pipe_o.lsu_reg_offset         <= 2'b0;
      id_ex_pipe_o.lsu_atop               <= 5'b0;
      id_ex_pipe_o.lsu_prepost_useincr    <= 1'b1;

      id_ex_pipe_o.pc                     <= 32'b0;

      id_ex_pipe_o.branch_in_ex           <= 1'b0;

      id_ex_pipe_o.trigger_match          <= 1'b0;

      // Signals for exception handling
      id_ex_pipe_o.instr                  <= INST_RESP_RESET_VAL;
      id_ex_pipe_o.instr_meta             <= '0;
      id_ex_pipe_o.illegal_insn           <= 1'b0;
      id_ex_pipe_o.ebrk_insn              <= 1'b0;
      id_ex_pipe_o.wfi_insn               <= 1'b0;
      id_ex_pipe_o.ecall_insn             <= 1'b0;
      id_ex_pipe_o.fencei_insn            <= 1'b0;
      id_ex_pipe_o.mret_insn              <= 1'b0;
      id_ex_pipe_o.dret_insn              <= 1'b0;
      id_ex_pipe_o.xif_insn               <= 1'b0;

    end else begin
      // normal pipeline unstall case
      if (id_valid_o && ex_ready_i) begin
        id_ex_pipe_o.instr_valid  <= 1'b1;
        
        id_ex_pipe_o.alu_en                 <= alu_en;

        // operand_c used by both ALU and LSU
        if (alu_en || lsu_en)
        begin
          id_ex_pipe_o.operand_c            <= operand_c;
        end

        // todo: alu_en is still set for LSU, could change to not setting alu_en and include lsu_en in if() below
        if (alu_en || div_en || csr_en || lsu_en) begin // todo: the addition of csr_en here is not SEC clean. However, csr_en should have been implied alu_en. Eventually this needs to become (alu_en || div_en || lsu_en) again.
          id_ex_pipe_o.alu_operator         <= alu_operator; // todo: not needed for LSU. Could be moved to a separate block
          id_ex_pipe_o.alu_operand_a        <= operand_a;
          id_ex_pipe_o.alu_operand_b        <= operand_b;
        end

        id_ex_pipe_o.div_en                 <= div_en;
        if (div_en) begin
          id_ex_pipe_o.div_operator         <= div_operator; // todo: consider letting div/rem use mul_operands
        end
        
        id_ex_pipe_o.mul_en                 <= mul_en;
        if (mul_en) begin
          id_ex_pipe_o.mul_operator         <= mul_operator;
          id_ex_pipe_o.mul_signed_mode      <= mul_signed_mode;
          id_ex_pipe_o.mul_operand_a        <= operand_a;
          id_ex_pipe_o.mul_operand_b        <= operand_b;
        end

        id_ex_pipe_o.rf_we                  <= rf_we || (xif_issue_if.x_issue_valid && xif_issue_if.x_issue_resp.writeback);
        if (rf_we) begin
          id_ex_pipe_o.rf_waddr             <= rf_waddr_o;
        end

        id_ex_pipe_o.csr_en                 <= csr_en;
        id_ex_pipe_o.csr_op                 <= csr_op;

        id_ex_pipe_o.lsu_en                 <= lsu_en;
        if (lsu_en) begin
          id_ex_pipe_o.lsu_we               <= lsu_we;
          id_ex_pipe_o.lsu_type             <= lsu_type;
          id_ex_pipe_o.lsu_sign_ext         <= lsu_sign_ext;
          id_ex_pipe_o.lsu_reg_offset       <= lsu_reg_offset;
          id_ex_pipe_o.lsu_atop             <= lsu_atop;
          id_ex_pipe_o.lsu_prepost_useincr  <= lsu_prepost_useincr;
        end

        id_ex_pipe_o.branch_in_ex           <= ctrl_transfer_insn_o == BRANCH_COND;

        // Propagate signals needed for exception handling in WB
        // TODO:OK:low Clock gating of pc if no existing exceptions
        //          and LSU it not in use
        id_ex_pipe_o.pc                     <= if_id_pipe_i.pc;

        if (if_id_pipe_i.instr_meta.compressed) begin
          // Overwrite instruction word in case of compressed instruction
          id_ex_pipe_o.instr.bus_resp.rdata <= {16'h0, if_id_pipe_i.compressed_instr};
          id_ex_pipe_o.instr.bus_resp.err   <= if_id_pipe_i.instr.bus_resp.err;
          id_ex_pipe_o.instr.mpu_status     <= if_id_pipe_i.instr.mpu_status;
        end
        else begin
          id_ex_pipe_o.instr                <= if_id_pipe_i.instr;
        end

        id_ex_pipe_o.instr_meta             <= instr_meta_n;

        // Exceptions and special instructions
        id_ex_pipe_o.illegal_insn           <= illegal_insn && !xif_insn_accept;
        id_ex_pipe_o.ebrk_insn              <= ebrk_insn;
        id_ex_pipe_o.wfi_insn               <= wfi_insn;
        id_ex_pipe_o.ecall_insn             <= ecall_insn;
        id_ex_pipe_o.fencei_insn            <= fencei_insn;
        id_ex_pipe_o.mret_insn              <= mret_insn;
        id_ex_pipe_o.dret_insn              <= dret_insn;
        id_ex_pipe_o.xif_insn               <= xif_insn_accept;

        id_ex_pipe_o.trigger_match          <= debug_trigger_match_id_i;
      end else if (ex_ready_i) begin
        id_ex_pipe_o.instr_valid            <= 1'b0;
      end
    end
  end

  assign csr_en_o = csr_en;
  assign csr_op_o = csr_op;

  // stall control for multicyle ID instructions (currently only misaligned LSU)
  assign multi_cycle_id_stall = 1'b0; //todo:ok Zce push/pop will use this

  // Stage ready/valid
  //
  // Most stall conditions are factored into halt_id (and will force both ready and valid to 0).
  //
  // Multi-cycle instruction related stalls are different; in that case ready will be 0 (as ID already
  // contains the instruction following the multicycle instruction.
  // todo: update when Zce is included. Currently, no multi cycle ID stalls are possible.

  assign id_ready_o = ctrl_fsm_i.kill_id || (!multi_cycle_id_stall && ex_ready_i && !ctrl_fsm_i.halt_id && !xif_waiting);

  // multi_cycle_id_stall is currently tied to 1'b0. Will be used for Zce push/pop instructions.
  assign id_valid_o = (instr_valid && !xif_waiting) || (multi_cycle_id_stall && !ctrl_fsm_i.kill_id && !ctrl_fsm_i.halt_id);


  //---------------------------------------------------------------------------
  // eXtension interface
  //---------------------------------------------------------------------------

  // remember whether an instruction was accepted or rejected (required if EX stage is not ready)
  logic xif_accepted_q, xif_rejected_q;
  always_ff @(posedge clk, negedge rst_n) begin : ID_XIF_STATE_REGISTERS
    if (rst_n == 1'b0) begin
      xif_accepted_q <= 1'b0;
      xif_rejected_q <= 1'b0;
    end else begin
      xif_accepted_q <= !(id_valid_o && ex_ready_i) && xif_insn_accept;
      xif_rejected_q <= !(id_valid_o && ex_ready_i) && xif_insn_reject;
    end
  end

  // attempt to offload every valid instruction that is considered illegal by the decoder
  assign xif_issue_if.x_issue_valid         = instr_valid && illegal_insn && !xif_accepted_q && !xif_rejected_q;

  assign xif_issue_if.x_issue_req.instr     = instr;
  assign xif_issue_if.x_issue_req.mode      = '0; // TODO: use the actual mode
  assign xif_issue_if.x_issue_req.id        = '0; // TODO: use an actual id instead of 0
  always_comb begin
    xif_issue_if.x_issue_req.rs       = '0;
    xif_issue_if.x_issue_req.rs_valid = '0;
    if (xif_issue_if.X_NUM_RS > 0) begin
      xif_issue_if.x_issue_req.rs      [0] = operand_a_fw;
      xif_issue_if.x_issue_req.rs_valid[0] = 1'b1;
    end
    if (xif_issue_if.X_NUM_RS > 1) begin
      xif_issue_if.x_issue_req.rs      [1] = operand_b_fw;
      xif_issue_if.x_issue_req.rs_valid[1] = 1'b1;
    end
    // TODO: check if forwarding is needed for other operands than rs1 and rs2
    for (integer i = 2; i < xif_issue_if.X_NUM_RS && i < REGFILE_NUM_READ_PORTS; i++) begin
      xif_issue_if.x_issue_req.rs      [i] = regfile_rdata_i[i];
      xif_issue_if.x_issue_req.rs_valid[i] = 1'b1;
    end
  end
  assign xif_issue_if.x_issue_req.frs       = '{default: '0};
  assign xif_issue_if.x_issue_req.frs_valid = '0;

  // need to wait if the coprocessor is not ready and has not already accepted or rejected the instruction
  assign xif_waiting = xif_issue_if.x_issue_valid && !xif_issue_if.x_issue_ready && !xif_accepted_q && !xif_rejected_q;

  // an instruction was offloaded successfully if the coprocessor accepts it (or has accepted it)
  assign xif_insn_accept = (xif_issue_if.x_issue_valid && xif_issue_if.x_issue_ready &&  xif_issue_if.x_issue_resp.accept) || xif_accepted_q;
  assign xif_insn_reject = (xif_issue_if.x_issue_valid && xif_issue_if.x_issue_ready && !xif_issue_if.x_issue_resp.accept) || xif_rejected_q;

endmodule // cv32e40x_id_stage
