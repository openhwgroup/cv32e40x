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

    input  logic        deassert_we_i,

    // Jumps and branches
    input  logic        branch_decision_i,
    output logic [31:0] jmp_target_o,
    
    // IF and ID stage signals

    output logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction
    input  logic        wb_ready_i,     // WB stage is ready for the next instruction

    output logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done
 
    // IF/ID pipeline
    input if_id_pipe_t if_id_pipe_i,

    // ID/EX pipeline 
    output id_ex_pipe_t id_ex_pipe_o,

    // From controller FSM
    input  ctrl_fsm_t   ctrl_fsm_i,

    input  PrivLvl_t    current_priv_lvl_i,

    // Debug Signal
    input  logic        debug_trigger_match_id_i,

    // Register file write back and forwards
    input  logic [31:0]    rf_wdata_wb_i,
    input  logic [31:0]    rf_wdata_wb_alu_i,

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

    input  logic        perf_imiss_i,

    input  logic        data_req_wb_i,

    output logic        mret_insn_o,
    output logic        dret_insn_o,
    // Decoder to controller
    output logic        csr_status_o,
    output logic        csr_en_o,
    output csr_opcode_e csr_op_o,

    output logic [1:0]  ctrl_transfer_insn_o,
    output logic [1:0]  ctrl_transfer_insn_raw_o,

    // RF interface -> controller
    output logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_o,
    output rf_addr_t    rf_raddr_o[REGFILE_NUM_READ_PORTS],
    output rf_addr_t    rf_waddr_o,

    output logic        regfile_alu_we_id_o,
    
    // Forwarding from controller
    input  op_fw_mux_e    operand_a_fw_mux_sel_i,
    input  op_fw_mux_e    operand_b_fw_mux_sel_i,
    input  jalr_fw_mux_e  jalr_fw_mux_sel_i,

    // Halt and stalls from controller
    input  logic          misaligned_stall_i,
    input  logic          jr_stall_i,
    input  logic          load_stall_i,
    input  logic          csr_stall_i,
    input  logic          wfi_stall_i,

    // Register file
    input  rf_data_t    regfile_rdata_i[REGFILE_NUM_READ_PORTS]

  
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

  // Register Write Control
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
  logic        csr_en;
  csr_opcode_e csr_op;
  
  logic        prepost_useincr;

  logic [31:0] operand_a_fw;
  logic [31:0] operand_b_fw;

  logic [31:0] jalr_fw;

  logic [31:0] operand_b;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  logic [31:0] operand_c;

  // Performance counters
  logic        id_valid_q;
  logic        minstret;

  // Branch target address
  logic [31:0] bch_target;

  // Stall for multicycle ID instructions
  logic multi_cycle_id_stall;

  logic is_last; // Indicates that an instruction is in its last ID phase

  // Special insn to travel down pipeline structs
  logic        illegal_insn;
  logic        ecall_insn;
  logic        mret_insn;
  logic        dret_insn;
  logic        wfi_insn;
  logic        ebrk_insn;
  logic        fencei_insn;

  // Local instruction valid qualifier
  logic        instr_valid;

  assign instr_valid = if_id_pipe_i.instr_valid && !ctrl_fsm_i.kill_id;

  assign mret_insn_o = mret_insn;
  assign dret_insn_o = dret_insn;

  assign is_last = !multi_cycle_id_stall;

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

  cv32e40x_pc_target
  cv32e40x_pc_target_i
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
    case (operand_a_fw_mux_sel_i)
      SEL_FW_EX:    operand_a_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_a_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_a_fw = regfile_rdata_i[0];
      default:      operand_a_fw = regfile_rdata_i[0];
    endcase; // case (operand_a_fw_mux_sel_i)
  end
  

  always_comb begin: jalr_fw_mux
    case (jalr_fw_mux_sel_i)
      SELJ_FW_WB:   jalr_fw = rf_wdata_wb_alu_i;
      SELJ_REGFILE: jalr_fw = regfile_rdata_i[0];
      default:      jalr_fw = regfile_rdata_i[0];
    endcase // jalr_fw_mux_sel_i
  end // jalr_fw_mux

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
    case (operand_b_fw_mux_sel_i)
      SEL_FW_EX:    operand_b_fw = rf_wdata_ex_i;
      SEL_FW_WB:    operand_b_fw = rf_wdata_wb_i;
      SEL_REGFILE:  operand_b_fw = regfile_rdata_i[1];
      default:      operand_b_fw = regfile_rdata_i[1];
    endcase; // case (operand_b_fw_mux_sel_i)
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
      .A_EXTENSION             ( A_EXTENSION            ),
      .USE_PMP                 ( USE_PMP                ),
      .DEBUG_TRIGGER_EN        ( DEBUG_TRIGGER_EN       )
      )
  decoder_i
  (
    // controller related signals
    .deassert_we_i                   ( deassert_we_i             ),

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
    .mult_en_o                       ( mult_en                   ),
    .mult_operator_o                 ( mult_operator             ),
    .mult_signed_mode_o              ( mult_signed_mode          ),

    // Register file control signals
    .rf_re_o                         ( rf_re_o                   ),
    .rf_we_o                         ( rf_we                     ),
    .rf_we_raw_o                     ( rf_we_raw                 ),

    // CSR control signals
    .csr_en_o                        ( csr_en                    ),
    .csr_status_o                    ( csr_status_o              ),
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
    .debug_mode_i                    ( ctrl_fsm_i.debug_mode   ), // TODO: pass on ctrl_fsm_i
    .debug_wfi_no_sleep_i            ( ctrl_fsm_i.debug_wfi_no_sleep      ),

    // jump/branches
    .ctrl_transfer_insn_o            ( ctrl_transfer_insn_o      ),
    .ctrl_transfer_insn_raw_o        ( ctrl_transfer_insn_raw_o  ),
    .ctrl_transfer_target_mux_sel_o  ( ctrl_transfer_target_mux_sel )
  );

  assign regfile_alu_we_id_o = rf_we_raw && !data_req_raw;

  
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
      id_ex_pipe_o.instr_valid            <= 1'b0;
      id_ex_pipe_o.alu_en                 <= '0;
      id_ex_pipe_o.alu_operator           <= ALU_SLTU;
      id_ex_pipe_o.alu_operand_a          <= '0;
      id_ex_pipe_o.alu_operand_b          <= '0;

      id_ex_pipe_o.operand_c              <= '0;

      id_ex_pipe_o.mult_en                <= 1'b0;
      id_ex_pipe_o.mult_operator          <= MUL_M32;
      id_ex_pipe_o.mult_operand_a         <= '0;
      id_ex_pipe_o.mult_operand_b         <= '0;
      id_ex_pipe_o.mult_signed_mode       <= 2'b00;

      id_ex_pipe_o.rf_we                  <= 1'b0;
      id_ex_pipe_o.rf_waddr               <= '0;

      id_ex_pipe_o.prepost_useincr        <= 1'b1;

      id_ex_pipe_o.csr_access             <= 1'b0;
      id_ex_pipe_o.csr_en                 <= 1'b0;
      id_ex_pipe_o.csr_op                 <= CSR_OP_READ;

      id_ex_pipe_o.data_req               <= 1'b0;
      id_ex_pipe_o.data_we                <= 1'b0;
      id_ex_pipe_o.data_type              <= 2'b0;
      id_ex_pipe_o.data_sign_ext          <= 1'b0;
      id_ex_pipe_o.data_reg_offset        <= 2'b0;
      id_ex_pipe_o.data_misaligned        <= 1'b0;
      id_ex_pipe_o.data_atop              <= 5'b0;

      id_ex_pipe_o.pc                     <= 32'h00000000;

      id_ex_pipe_o.branch_in_ex           <= 1'b0;

      id_ex_pipe_o.trigger_match          <= 1'b0;
      // Signals for exception handling
      id_ex_pipe_o.instr                  <= INST_RESP_RESET_VAL;
      id_ex_pipe_o.illegal_insn           <= 1'b0;
      id_ex_pipe_o.ebrk_insn              <= 1'b0;
      id_ex_pipe_o.wfi_insn               <= 1'b0;
      id_ex_pipe_o.ecall_insn             <= 1'b0;
      id_ex_pipe_o.fencei_insn            <= 1'b0;
      id_ex_pipe_o.mret_insn              <= 1'b0;
      id_ex_pipe_o.dret_insn              <= 1'b0;

    end else begin
      // normal pipeline unstall case

      if (id_valid_o)
      begin // unstall the whole pipeline
        id_ex_pipe_o.instr_valid  <= 1'b1;
        if (misaligned_stall_i) begin
          // misaligned data access case
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
        end else begin // !misaligned_stall_i
          id_ex_pipe_o.alu_en                 <= alu_en;
          if (alu_en)
          begin
            id_ex_pipe_o.alu_operator         <= alu_operator;
            id_ex_pipe_o.alu_operand_a        <= alu_operand_a;
            id_ex_pipe_o.alu_operand_b        <= alu_operand_b;
            id_ex_pipe_o.operand_c            <= operand_c;
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
            id_ex_pipe_o.rf_waddr             <= rf_waddr_o;
          end

          id_ex_pipe_o.prepost_useincr        <= prepost_useincr;

          id_ex_pipe_o.csr_access             <= csr_en;
          id_ex_pipe_o.csr_en                 <= csr_en;
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

          id_ex_pipe_o.data_misaligned <= 1'b0;

          id_ex_pipe_o.branch_in_ex    <= ctrl_transfer_insn_o == BRANCH_COND;

          // Propagate signals needed for exception handling in WB
          // TODO:OK: Clock gating of pc if no existing exceptions
          //          and LSU it not in use
          id_ex_pipe_o.pc              <= if_id_pipe_i.pc;

          if (if_id_pipe_i.is_compressed) begin
            // Overwrite instruction word in case of compressed instruction
            id_ex_pipe_o.instr.bus_resp.rdata <= {16'h0, if_id_pipe_i.compressed_instr};
            id_ex_pipe_o.instr.bus_resp.err   <= if_id_pipe_i.instr.bus_resp.err;
            id_ex_pipe_o.instr.mpu_status     <= if_id_pipe_i.instr.mpu_status;
          end
          else begin
            id_ex_pipe_o.instr                <= if_id_pipe_i.instr;
          end

          // Exceptions and special instructions
          id_ex_pipe_o.illegal_insn           <= illegal_insn;
          id_ex_pipe_o.ebrk_insn              <= ebrk_insn;
          id_ex_pipe_o.wfi_insn               <= wfi_insn;
          id_ex_pipe_o.ecall_insn             <= ecall_insn;
          id_ex_pipe_o.fencei_insn            <= fencei_insn;
          id_ex_pipe_o.mret_insn              <= mret_insn;
          id_ex_pipe_o.dret_insn              <= dret_insn;

          id_ex_pipe_o.trigger_match          <= debug_trigger_match_id_i;
        end
      end else if (ex_ready_i) begin
        // EX stage is ready but we don't have a new instruction for it,
        // so we set all instr_valid to 0 (stage will use this to locally gate *enables)
        id_ex_pipe_o.instr_valid            <= 1'b0;
        
      end else if (id_ex_pipe_o.csr_access) begin // TODO: We should get rid of this special case
       //In the EX stage there was a CSR access. To avoid multiple
       //writes to the RF, disable csr_access (cs_registers will keep it's rdata as it was when csr_access was 1'b1).
       //Not doing it can overwrite the RF file with the currennt CSR value rather than the old one
       id_ex_pipe_o.csr_access              <= 1'b0;
      end
    end
  end

  // Performance Counter Events
  //TODO:OK: Fix counters to reflect new controller behaviour
  // Illegal/ebreak/ecall are never counted as retired instructions. Note that actually issued instructions
  // are being counted; the manner in which CSR instructions access the performance counters guarantees
  // that this count will correspond to the retired isntructions count.
  assign minstret = id_valid_o && ctrl_fsm_i.is_decoding && is_last && !(illegal_insn || ebrk_insn || ecall_insn);

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
      // Helper signal, id_valid may be 1'b1 to update EX for misaligned LSU, gate off to not count events in those cases
      id_valid_q                 <= id_valid_o && is_last;
      // ID stage counts
      mhpmevent_minstret_o       <= minstret;
      mhpmevent_load_o           <= minstret && data_req && !data_we;
      mhpmevent_store_o          <= minstret && data_req && data_we;
      mhpmevent_jump_o           <= minstret && ((ctrl_transfer_insn_o == BRANCH_JAL) || (ctrl_transfer_insn_o == BRANCH_JALR));
      mhpmevent_branch_o         <= minstret && (ctrl_transfer_insn_o == BRANCH_COND);
      mhpmevent_compressed_o     <= minstret && if_id_pipe_i.is_compressed;
      // EX stage count
      mhpmevent_branch_taken_o   <= mhpmevent_branch_o && branch_decision_i;
      // IF stage count
      mhpmevent_imiss_o          <= perf_imiss_i;
      // Jump-register-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_jr_stall_o       <= jr_stall_i && !ctrl_fsm_i.halt_id && id_valid_q;
      // Load-use-hazard; do not count stall on flushed instructions (id_valid_q used to only count first cycle)
      mhpmevent_ld_stall_o       <= load_stall_i && !ctrl_fsm_i.halt_id && id_valid_q;
    end
  end

  assign csr_en_o = csr_en;
  assign csr_op_o = csr_op;

  // stall control for multicyle ID instructions (currently only misaligned LSU)
  assign multi_cycle_id_stall = misaligned_stall_i;

  //TODO:OK: Added description of how halt_<stage> signals work (how are multicycle insn treated)
  //TODO:OK Halt and stall seems to be the same
  assign id_ready_o = ctrl_fsm_i.kill_id || (!csr_stall_i && !multi_cycle_id_stall && !jr_stall_i && !load_stall_i && ex_ready_i && !ctrl_fsm_i.halt_id && !wfi_stall_i);
  assign id_valid_o = (instr_valid && id_ready_o) || (multi_cycle_id_stall && ex_ready_i); // Allow ID to update id_ex_pipe for misaligned load/stores regardless of halt/ready


endmodule // cv32e40x_id_stage
