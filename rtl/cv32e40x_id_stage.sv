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
  parameter DEBUG_TRIGGER_EN        =  1,
  parameter REGFILE_NUM_READ_PORTS  =  2,
  parameter REGFILE_NUM_WRITE_PORTS =  2
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
    input  logic              instr_valid_i,
    input  logic       [31:0] instr_rdata_i,      // comes from pipeline of IF stage
    output logic              instr_req_o,
    input  logic              is_compressed_i,
    input  logic              illegal_c_insn_i,

    // Jumps and branches
    output logic        branch_in_ex_o,
    input  logic        branch_decision_i,
    output logic [31:0] jump_target_o,

    // IF and ID stage signals
    output logic        clear_instr_valid_o,
    output logic        pc_set_o,
    output pc_mux_e     pc_mux_o,
    output exc_pc_mux_e exc_pc_mux_o,

    input  logic        is_fetch_failed_i,

    input  logic [31:0] pc_id_i,

    // Stalls
    output logic        halt_if_o,      // controller requests a halt of the IF stage

    output logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction
    input  logic        wb_ready_i,     // WB stage is ready for the next instruction

    output logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done

    // Pipeline ID/EX
    output logic [31:0] pc_ex_o,

    output logic [31:0] alu_operand_a_ex_o,
    output logic [31:0] alu_operand_b_ex_o,
    output logic [31:0] alu_operand_c_ex_o,

    output logic [4:0]  regfile_waddr_ex_o,
    output logic        regfile_we_ex_o,

    output logic [4:0]  regfile_alu_waddr_ex_o,
    output logic        regfile_alu_we_ex_o,

    // ALU
    output logic        alu_en_ex_o,
    output alu_opcode_e alu_operator_ex_o,

    // MUL
    output mul_opcode_e  mult_operator_ex_o,
    output logic [31:0]  mult_operand_a_ex_o,
    output logic [31:0]  mult_operand_b_ex_o,
    output logic [31:0]  mult_operand_c_ex_o,
    output logic         mult_en_ex_o,
    output logic         mult_sel_subword_ex_o,
    output logic [ 1:0]  mult_signed_mode_ex_o,

    // CSR ID/EX
    output logic        csr_access_ex_o,
    output csr_opcode_e csr_op_ex_o,
    input  PrivLvl_t    current_priv_lvl_i,
    output logic [5:0]  csr_cause_o,
    output logic        csr_save_if_o,
    output logic        csr_save_id_o,
    output logic        csr_save_ex_o,
    output logic        csr_restore_mret_id_o,
    output logic        csr_restore_dret_id_o,
    output logic        csr_save_cause_o,

    // Interface to load store unit
    output logic        data_req_ex_o,
    output logic        data_we_ex_o,
    output logic [1:0]  data_type_ex_o,
    output logic [1:0]  data_sign_ext_ex_o,
    output logic [1:0]  data_reg_offset_ex_o,

    output logic        data_misaligned_ex_o,

    output logic        prepost_useincr_ex_o,
    input  logic        data_misaligned_i,
    input  logic        data_err_i,
    output logic        data_err_ack_o,

    output logic [5:0]  atop_ex_o,

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

    // Forward Signals
    input  logic [4:0]  regfile_waddr_wb_i,
    input  logic        regfile_we_wb_i,
    input  logic [31:0] regfile_wdata_wb_i, // From wb_stage: selects data from data memory, ex_stage result and sp rdata

    input  logic [4:0]  regfile_alu_waddr_fw_i,
    input  logic        regfile_alu_we_fw_i,
    input  logic [31:0] regfile_alu_wdata_fw_i,

    // from ALU
    input  logic        mult_multicycle_i,    // when we need multiple cycles in the multiplier and use op c as storage

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

  logic        illegal_insn_dec;
  logic        ebrk_insn_dec;
  logic        mret_insn_dec;

  logic        dret_insn_dec;

  logic        ecall_insn_dec;
  logic        wfi_insn_dec;

  logic        fencei_insn_dec;

  logic [REGFILE_NUM_READ_PORTS-1:0] reg_used_dec;

  logic        branch_taken_ex;
  logic [1:0]  ctrl_transfer_insn_in_id;
  logic [1:0]  ctrl_transfer_insn_in_dec;

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

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  logic [31:0] jump_target;       // calculated jump target (-> EX -> IF)

  // Signals running between controller and int_controller
  logic       irq_req_ctrl;
  logic       irq_wu_ctrl;
  logic [4:0] irq_id_ctrl;

  // Register file read interface
  logic [REGFILE_NUM_READ_PORTS-1:0][4:0]  regfile_raddr;
  logic [REGFILE_NUM_READ_PORTS-1:0][31:0] regfile_rdata;

  // Register file write interface
  logic [REGFILE_NUM_WRITE_PORTS-1:0] [4:0] regfile_waddr;
  logic [REGFILE_NUM_WRITE_PORTS-1:0] [31:0] regfile_wdata;
  logic [REGFILE_NUM_WRITE_PORTS-1:0] regfile_we;
  
  logic [4:0]  regfile_waddr_id;
  logic [4:0]  regfile_alu_waddr_id;
  logic        regfile_alu_we_id, regfile_alu_we_dec_id;

  
  // ALU Control
  logic        alu_en;
  alu_opcode_e alu_operator;
  logic [2:0]  alu_op_a_mux_sel;
  logic [2:0]  alu_op_b_mux_sel;
  logic [1:0]  alu_op_c_mux_sel;

  logic [0:0]  imm_a_mux_sel;
  logic [3:0]  imm_b_mux_sel;
  logic [1:0]  ctrl_transfer_target_mux_sel;

  // Multiplier Control
  mul_opcode_e mult_operator;    // multiplication operation selection
  logic        mult_en;          // multiplication is used instead of ALU
  logic        mult_int_en;      // use integer multiplier
  logic        mult_sel_subword; // Select a subword when doing multiplications
  logic [1:0]  mult_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers

  // Register Write Control
  logic        regfile_we_id;

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic [1:0]  data_sign_ext_id;
  logic [1:0]  data_reg_offset_id;
  logic        data_req_id;

  // Atomic memory instruction
  logic [5:0]  atop_id;

  // CSR control
  logic        csr_access;
  csr_opcode_e csr_op;
  logic        csr_status;

  logic        prepost_useincr;

  // Forwarding
  logic [1:0]  operand_a_fw_mux_sel;
  logic [1:0]  operand_b_fw_mux_sel;
  logic [1:0]  operand_c_fw_mux_sel;
  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;
  logic [31:0] operand_c_fw_id;

  logic [31:0] operand_b;
  logic [31:0] operand_c;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] alu_operand_c;

  // Forwarding detection signals
  logic [REGFILE_NUM_READ_PORTS-1:0] reg_in_ex_matches_reg_in_dec;
  logic [REGFILE_NUM_READ_PORTS-1:0] reg_in_wb_matches_reg_in_dec;
  logic [REGFILE_NUM_READ_PORTS-1:0] reg_in_alu_matches_reg_in_dec;

  logic        mret_dec;
  logic        dret_dec;

  // Performance counters
  logic        id_valid_q;
  logic        minstret;

  

  assign instr = instr_rdata_i;


  // immediate extraction and sign extension
  assign imm_i_type  = { {20 {instr[31]}}, instr[31:20] };
  assign imm_s_type  = { {20 {instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_sb_type = { {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type  = { instr[31:12], 12'b0 };
  assign imm_uj_type = { {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign imm_z_type  = { 27'b0, instr[REG_S1_MSB:REG_S1_LSB] };


  //---------------------------------------------------------------------------
  // source register selection regfile_fp_x=1 <=> CV32E40P_REG_x is a FP-register
  //---------------------------------------------------------------------------
  assign regfile_raddr[0] = instr[REG_S1_MSB:REG_S1_LSB];
  assign regfile_raddr[1] = instr[REG_S2_MSB:REG_S2_LSB];


  //---------------------------------------------------------------------------
  // destination registers regfile_fp_d=1 <=> REG_D is a FP-register
  //---------------------------------------------------------------------------
  assign regfile_waddr_id = instr[REG_D_MSB:REG_D_LSB];

  // Second Register Write Address Selection
  // Used for prepost load/store and multiplier
  assign regfile_alu_waddr_id = regfile_waddr_id;

  // Forwarding control signals
  genvar i;
  generate
    for(i=0; i<REGFILE_NUM_READ_PORTS; i++) begin : gen_forward_signals
      assign reg_in_ex_matches_reg_in_dec[i]  = (regfile_waddr_ex_o     == regfile_raddr[i]) && (reg_used_dec[i] == 1'b1) && (regfile_raddr[i] != '0);
      assign reg_in_wb_matches_reg_in_dec[i]  = (regfile_waddr_wb_i     == regfile_raddr[i]) && (reg_used_dec[i] == 1'b1) && (regfile_raddr[i] != '0);
      assign reg_in_alu_matches_reg_in_dec[i] = (regfile_alu_waddr_fw_i == regfile_raddr[i]) && (reg_used_dec[i] == 1'b1) && (regfile_raddr[i] != '0);
    end
  endgenerate

  // kill instruction in the IF/ID stage by setting the instr_valid_id control
  // signal to 0 for instructions that are done
  assign clear_instr_valid_o = id_ready_o | halt_id | branch_taken_ex;

  assign branch_taken_ex = branch_in_ex_o && branch_decision_i;


  assign mult_en = mult_int_en;


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
      JT_JAL:  jump_target = pc_id_i + imm_uj_type;
      JT_COND: jump_target = pc_id_i + imm_sb_type;

      // JALR: Cannot forward RS1, since the path is too long
      JT_JALR: jump_target = regfile_rdata[0] + imm_i_type;
      default:  jump_target = regfile_rdata[0] + imm_i_type;
    endcase
  end

  assign jump_target_o = jump_target;


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
      OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw_id;
      OP_A_REGB_OR_FWD:  alu_operand_a = operand_b_fw_id;
      OP_A_CURRPC:       alu_operand_a = pc_id_i;
      OP_A_IMM:          alu_operand_a = imm_a;
      default:           alu_operand_a = operand_a_fw_id;
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
      SEL_FW_EX:    operand_a_fw_id = regfile_alu_wdata_fw_i;
      SEL_FW_WB:    operand_a_fw_id = regfile_wdata_wb_i;
      SEL_REGFILE:  operand_a_fw_id = regfile_rdata[0];
      default:      operand_a_fw_id = regfile_rdata[0];
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
      IMMB_PCINCR: imm_b = is_compressed_i ? 32'h2 : 32'h4;
      default:     imm_b = imm_i_type;
    endcase
  end

  // ALU_Op_b Mux
  always_comb begin : alu_operand_b_mux
    case (alu_op_b_mux_sel)
      OP_B_REGA_OR_FWD:  operand_b = operand_a_fw_id;
      OP_B_REGB_OR_FWD:  operand_b = operand_b_fw_id;
      OP_B_IMM:          operand_b = imm_b;
      default:           operand_b = operand_b_fw_id;
    endcase // case (alu_op_b_mux_sel)
  end


  // choose normal or scalar replicated version of operand b
  assign alu_operand_b = operand_b;


  // Operand b forwarding mux
  always_comb begin : operand_b_fw_mux
    case (operand_b_fw_mux_sel)
      SEL_FW_EX:    operand_b_fw_id = regfile_alu_wdata_fw_i;
      SEL_FW_WB:    operand_b_fw_id = regfile_wdata_wb_i;
      SEL_REGFILE:  operand_b_fw_id = regfile_rdata[1];
      default:      operand_b_fw_id = regfile_rdata[1];
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
      OP_C_REGB_OR_FWD:  operand_c = operand_b_fw_id;
      OP_C_JT:           operand_c = jump_target;
      default:           operand_c = operand_c_fw_id;
    endcase // case (alu_op_c_mux_sel)
  end

// choose normal or scalar replicated version of operand b
  assign alu_operand_c = operand_c;

  // Operand c forwarding mux
  always_comb begin : operand_c_fw_mux
    case (operand_c_fw_mux_sel)
      SEL_FW_EX:    operand_c_fw_id = regfile_alu_wdata_fw_i;
      SEL_REGFILE:  operand_c_fw_id = 32'h00000000;
      default:      operand_c_fw_id = 32'h00000000;
    endcase; // case (operand_c_fw_mux_sel)
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
  assign regfile_waddr[0] = regfile_waddr_wb_i;
  assign regfile_waddr[1] = regfile_alu_waddr_fw_i;

  assign regfile_wdata[0] = regfile_wdata_wb_i;
  assign regfile_wdata[1] = regfile_alu_wdata_fw_i;

  assign regfile_we[0] = regfile_we_wb_i;
  assign regfile_we[1] = regfile_alu_we_fw_i;

  cv32e40x_register_file_wrapper
  #(
    .ADDR_WIDTH         ( 5                      ),
    .DATA_WIDTH         ( 32                     ),
    .NUM_READ_PORTS     ( REGFILE_NUM_READ_PORTS ),
    .NUM_WRITE_PORTS    ( REGFILE_NUM_WRITE_PORTS)
  )
  register_file_wrapper_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_n              ),

    .scan_cg_en_i       ( scan_cg_en_i       ),

    // Read ports
    .raddr_i            ( regfile_raddr      ),
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
      .DEBUG_TRIGGER_EN        ( DEBUG_TRIGGER_EN       ),
      .REGFILE_NUM_READ_PORTS ( REGFILE_NUM_READ_PORTS )
      )
  decoder_i
  (
    // controller related signals
    .deassert_we_i                   ( deassert_we               ),

    .illegal_insn_o                  ( illegal_insn_dec          ),
    .ebrk_insn_o                     ( ebrk_insn_dec             ),

    .mret_insn_o                     ( mret_insn_dec             ),
    .dret_insn_o                     ( dret_insn_dec             ),

    .mret_dec_o                      ( mret_dec                  ),
    .dret_dec_o                      ( dret_dec                  ),

    .ecall_insn_o                    ( ecall_insn_dec            ),
    .wfi_o                           ( wfi_insn_dec              ),

    .fencei_insn_o                   ( fencei_insn_dec           ),

    .reg_used_o                      ( reg_used_dec              ),
    
    // from IF/ID pipeline
    .instr_rdata_i                   ( instr                     ),
    .illegal_c_insn_i                ( illegal_c_insn_i          ),

    // ALU signals
    .alu_en_o                        ( alu_en                    ),
    .alu_operator_o                  ( alu_operator              ),
    .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel          ),
    .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel          ),
    .alu_op_c_mux_sel_o              ( alu_op_c_mux_sel          ),
    .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
    .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),

    // MUL signals
    .mult_operator_o                 ( mult_operator             ),
    .mult_int_en_o                   ( mult_int_en               ),
    .mult_sel_subword_o              ( mult_sel_subword          ),
    .mult_signed_mode_o              ( mult_signed_mode          ),

    // Register file control signals
    .regfile_mem_we_o                ( regfile_we_id             ),
    .regfile_alu_we_o                ( regfile_alu_we_id         ),
    .regfile_alu_we_dec_o            ( regfile_alu_we_dec_id     ),

    // CSR control signals
    .csr_access_o                    ( csr_access                ),
    .csr_status_o                    ( csr_status                ),
    .csr_op_o                        ( csr_op                    ),
    .current_priv_lvl_i              ( current_priv_lvl_i        ),

    // Data bus interface
    .data_req_o                      ( data_req_id               ),
    .data_we_o                       ( data_we_id                ),
    .prepost_useincr_o               ( prepost_useincr           ),
    .data_type_o                     ( data_type_id              ),
    .data_sign_extension_o           ( data_sign_ext_id          ),
    .data_reg_offset_o               ( data_reg_offset_id        ),

    // Atomic memory access
    .atop_o                          ( atop_id                   ),

    // debug mode
    .debug_mode_i                    ( debug_mode_o              ),
    .debug_wfi_no_sleep_i            ( debug_wfi_no_sleep        ),

    // jump/branches
    .ctrl_transfer_insn_in_dec_o     ( ctrl_transfer_insn_in_dec    ),
    .ctrl_transfer_insn_in_id_o      ( ctrl_transfer_insn_in_id     ),
    .ctrl_transfer_target_mux_sel_o  ( ctrl_transfer_target_mux_sel )

  );

  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////

  cv32e40x_controller
  #(
    .REGFILE_NUM_READ_PORTS     ( REGFILE_NUM_READ_PORTS ),
    .REGFILE_NUM_WRITE_PORTS    ( REGFILE_NUM_WRITE_PORTS)
  )
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

    .illegal_insn_i                 ( illegal_insn_dec       ),
    .ecall_insn_i                   ( ecall_insn_dec         ),
    .mret_insn_i                    ( mret_insn_dec          ),

    .dret_insn_i                    ( dret_insn_dec          ),

    .mret_dec_i                     ( mret_dec               ),
    .dret_dec_i                     ( dret_dec               ),


    .wfi_i                          ( wfi_insn_dec           ),
    .ebrk_insn_i                    ( ebrk_insn_dec          ),
    .fencei_insn_i                  ( fencei_insn_dec        ),
    .csr_status_i                   ( csr_status             ),

    // from IF/ID pipeline
    .instr_valid_i                  ( instr_valid_i          ),

    // from prefetcher
    .instr_req_o                    ( instr_req_o            ),

    // to prefetcher
    .pc_set_o                       ( pc_set_o               ),
    .pc_mux_o                       ( pc_mux_o               ),
    .exc_pc_mux_o                   ( exc_pc_mux_o           ),
    .exc_cause_o                    ( exc_cause_o            ),

    .pc_id_i                        ( pc_id_i                ),
    .is_compressed_i                ( is_compressed_i        ),

    // LSU
    .data_req_ex_i                  ( data_req_ex_o          ),
    .data_we_ex_i                   ( data_we_ex_o           ),
    .data_misaligned_i              ( data_misaligned_i      ),

    // ALU
    .mult_multicycle_i              ( mult_multicycle_i      ),

    // jump/branch control
    .branch_taken_ex_i              ( branch_taken_ex        ),
    .ctrl_transfer_insn_in_id_i     ( ctrl_transfer_insn_in_id  ),
    .ctrl_transfer_insn_in_dec_i    ( ctrl_transfer_insn_in_dec ),

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

    // Write targets from ID
    .regfile_we_id_i                ( regfile_alu_we_dec_id  ),
    .regfile_alu_waddr_id_i         ( regfile_alu_waddr_id   ),

    // Forwarding signals from regfile
    .regfile_we_ex_i                ( regfile_we_ex_o        ),
    .regfile_waddr_ex_i             ( regfile_waddr_ex_o     ),
    .regfile_we_wb_i                ( regfile_we_wb_i        ),

    // regfile port 2
    .regfile_alu_we_fw_i            ( regfile_alu_we_fw_i    ),

    // Forwarding detection signals
    .reg_in_ex_matches_reg_in_dec_i    ( reg_in_ex_matches_reg_in_dec  ),
    .reg_in_wb_matches_reg_in_dec_i    ( reg_in_wb_matches_reg_in_dec  ),
    .reg_in_alu_matches_reg_in_dec_i   ( reg_in_alu_matches_reg_in_dec ),
    
    // Forwarding signals
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel   ),
    .operand_c_fw_mux_sel_o         ( operand_c_fw_mux_sel   ),

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
      alu_en_ex_o                 <= '0;
      alu_operator_ex_o           <= ALU_SLTU;
      alu_operand_a_ex_o          <= '0;
      alu_operand_b_ex_o          <= '0;
      alu_operand_c_ex_o          <= '0;

      mult_operator_ex_o          <= MUL_MAC32;
      mult_operand_a_ex_o         <= '0;
      mult_operand_b_ex_o         <= '0;
      mult_operand_c_ex_o         <= '0;
      mult_en_ex_o                <= 1'b0;
      mult_sel_subword_ex_o       <= 1'b0;
      mult_signed_mode_ex_o       <= 2'b00;

      regfile_waddr_ex_o          <= 6'b0;
      regfile_we_ex_o             <= 1'b0;

      regfile_alu_waddr_ex_o      <= 6'b0;
      regfile_alu_we_ex_o         <= 1'b0;
      prepost_useincr_ex_o        <= 1'b0;

      csr_access_ex_o             <= 1'b0;
      csr_op_ex_o                 <= CSR_OP_READ;

      data_we_ex_o                <= 1'b0;
      data_type_ex_o              <= 2'b0;
      data_sign_ext_ex_o          <= 2'b0;
      data_reg_offset_ex_o        <= 2'b0;
      data_req_ex_o               <= 1'b0;
      atop_ex_o                   <= 5'b0;

      data_misaligned_ex_o        <= 1'b0;

      pc_ex_o                     <= '0;

      branch_in_ex_o              <= 1'b0;

    end
    else if (data_misaligned_i) begin
      // misaligned data access case
      if (ex_ready_i)
      begin // misaligned access case, only unstall alu operands

        // if we are using post increments, then we have to use the
        // original value of the register for the second memory access
        // => keep it stalled
        if (prepost_useincr_ex_o == 1'b1)
        begin
          alu_operand_a_ex_o        <= operand_a_fw_id;
        end

        alu_operand_b_ex_o          <= 32'h4;
        regfile_alu_we_ex_o         <= 1'b0;
        prepost_useincr_ex_o        <= 1'b1;

        data_misaligned_ex_o        <= 1'b1;
      end
    end else if (mult_multicycle_i) begin
      mult_operand_c_ex_o <= operand_c_fw_id;
    end
    else begin
      // normal pipeline unstall case

      if (id_valid_o)
      begin // unstall the whole pipeline
        alu_en_ex_o                 <= alu_en;
        if (alu_en)
        begin
          alu_operator_ex_o         <= alu_operator;
          alu_operand_a_ex_o        <= alu_operand_a;
          alu_operand_b_ex_o        <= alu_operand_b;
          alu_operand_c_ex_o        <= alu_operand_c;
        end

        mult_en_ex_o                <= mult_en;
        if (mult_int_en) begin
          mult_operator_ex_o        <= mult_operator;
          mult_sel_subword_ex_o     <= mult_sel_subword;
          mult_signed_mode_ex_o     <= mult_signed_mode;
          mult_operand_a_ex_o       <= alu_operand_a;
          mult_operand_b_ex_o       <= alu_operand_b;
          mult_operand_c_ex_o       <= alu_operand_c;
        end
        
        regfile_we_ex_o             <= regfile_we_id;
        if (regfile_we_id) begin
          regfile_waddr_ex_o        <= regfile_waddr_id;
        end

        regfile_alu_we_ex_o         <= regfile_alu_we_id;
        if (regfile_alu_we_id) begin
          regfile_alu_waddr_ex_o    <= regfile_alu_waddr_id;
        end

        prepost_useincr_ex_o        <= prepost_useincr;

        csr_access_ex_o             <= csr_access;
        csr_op_ex_o                 <= csr_op;

        data_req_ex_o               <= data_req_id;
        if (data_req_id)
        begin // only needed for LSU when there is an active request
          data_we_ex_o              <= data_we_id;
          data_type_ex_o            <= data_type_id;
          data_sign_ext_ex_o        <= data_sign_ext_id;
          data_reg_offset_ex_o      <= data_reg_offset_id;
          atop_ex_o                 <= atop_id;
        end

        data_misaligned_ex_o        <= 1'b0;

        if ((ctrl_transfer_insn_in_id == BRANCH_COND) || data_req_id) begin
          pc_ex_o                   <= pc_id_i;
        end

        branch_in_ex_o              <= ctrl_transfer_insn_in_id == BRANCH_COND;
      end else if(ex_ready_i) begin
        // EX stage is ready but we don't have a new instruction for it,
        // so we set all write enables to 0, but unstall the pipe

        regfile_we_ex_o             <= 1'b0;

        regfile_alu_we_ex_o         <= 1'b0;

        csr_op_ex_o                 <= CSR_OP_READ;

        data_req_ex_o               <= 1'b0;

        data_misaligned_ex_o        <= 1'b0;

        branch_in_ex_o              <= 1'b0;

        alu_operator_ex_o           <= ALU_SLTU;

        mult_en_ex_o                <= 1'b0;

        alu_en_ex_o                 <= 1'b1;

      end else if (csr_access_ex_o) begin
       //In the EX stage there was a CSR access, to avoid multiple
       //writes to the RF, disable regfile_alu_we_ex_o.
       //Not doing it can overwrite the RF file with the currennt CSR value rather than the old one
       regfile_alu_we_ex_o         <= 1'b0;
      end
    end
  end

  // Performance Counter Events

  // Illegal/ebreak/ecall are never counted as retired instructions. Note that actually issued instructions
  // are being counted; the manner in which CSR instructions access the performance counters guarantees
  // that this count will correspond to the retired isntructions count.
  assign minstret = id_valid_o && is_decoding_o && !(illegal_insn_dec || ebrk_insn_dec || ecall_insn_dec);

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
      mhpmevent_load_o           <= minstret && data_req_id && !data_we_id;
      mhpmevent_store_o          <= minstret && data_req_id && data_we_id;
      mhpmevent_jump_o           <= minstret && ((ctrl_transfer_insn_in_id == BRANCH_JAL) || (ctrl_transfer_insn_in_id == BRANCH_JALR));
      mhpmevent_branch_o         <= minstret && (ctrl_transfer_insn_in_id == BRANCH_COND);
      mhpmevent_compressed_o     <= minstret && is_compressed_i;
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


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifdef CV32E40P_ASSERT_ON

    // make sure that branch decision is valid when jumping
    a_br_decision : assert property (
      @(posedge clk) (branch_in_ex_o) |-> (branch_decision_i !== 1'bx) ) else begin $warning("%t, Branch decision is X in module %m", $time); $stop; end

    // the instruction delivered to the ID stage should always be valid
    a_valid_instr : assert property (
      @(posedge clk) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr)) ) else $warning("%t, Instruction is valid, but has at least one X", $time);

    // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
    // and that EX stage is ready to receive flushed instruction immediately
    property p_branch_taken_ex;
       @(posedge clk) disable iff (!rst_n) (branch_taken_ex == 1'b1) |-> ((ex_ready_i == 1'b1) &&
                                                                          (alu_en == 1'b0) &&
                                                                          (mult_en == 1'b0) && (mult_int_en == 1'b0) &&
                                                                          (regfile_we_id == 1'b0) &&
                                                                          (regfile_alu_we_id == 1'b0) && (data_req_id == 1'b0));
    endproperty

    a_branch_taken_ex : assert property(p_branch_taken_ex);

    // Check that if IRQ PC update does not coincide with IRQ related CSR write
    // MIE is excluded from the check because it has a bypass.
    property p_irq_csr;
       @(posedge clk) disable iff (!rst_n) (pc_set_o && (pc_mux_o == PC_EXCEPTION) && ((exc_pc_mux_o == EXC_PC_EXCEPTION) || (exc_pc_mux_o == EXC_PC_IRQ)) &&
                                            csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)) |->
                                           ((alu_operand_b_ex_o[11:0] != CSR_MSTATUS) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MEPC) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MCAUSE) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MTVEC));
    endproperty

    a_irq_csr : assert property(p_irq_csr);

    // Check that xret does not coincide with CSR write (to avoid using wrong return address)
    // This check is more strict than really needed; a CSR instruction would be allowed in EX as long
    // as its write action happens before the xret CSR usage
    property p_xret_csr;
       @(posedge clk) disable iff (!rst_n) (pc_set_o && ((pc_mux_o == PC_MRET) || (pc_mux_o == PC_DRET))) |->
                                           (!(csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)));
    endproperty

    a_xret_csr : assert property(p_xret_csr);

    generate
    if (!A_EXTENSION) begin : gen_no_a_extension_assertions

      // Check that A extension opcodes are decoded as illegal when A extension not enabled
      property p_illegal_0;
         @(posedge clk) disable iff (!rst_n) (instr[6:0] == OPCODE_AMO) |-> (illegal_insn_dec == 'b1);
      endproperty

      a_illegal_0 : assert property(p_illegal_0);

    end
    endgenerate

    

   // Check that illegal instruction has no other side effects
    property p_illegal_2;
       @(posedge clk) disable iff (!rst_n) (illegal_insn_dec == 1'b1) |-> !(ebrk_insn_dec || mret_insn_dec || dret_insn_dec ||
                                                                            ecall_insn_dec || wfi_insn_dec || fencei_insn_dec ||
                                                                            alu_en || mult_int_en ||
                                                                            regfile_we_id || regfile_alu_we_id ||
                                                                            csr_op != CSR_OP_READ || data_req_id);
    endproperty

    a_illegal_2 : assert property(p_illegal_2);

  `endif

endmodule // cv32e40x_id_stage
