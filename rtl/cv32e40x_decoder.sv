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

module cv32e40x_decoder import cv32e40x_pkg::*; import cv32e40x_apu_core_pkg::*;
#(
  parameter PULP_XPULP        = 1,              // PULP ISA Extension (including PULP specific CSRs and hardware loop, excluding p.elw)
  parameter PULP_CLUSTER      =  0,
  parameter A_EXTENSION       = 0,
  parameter PULP_SECURE       = 0,
  parameter USE_PMP           = 0,
  parameter APU_WOP_CPU       = 6,
  parameter DEBUG_TRIGGER_EN  = 1
)
(
  // singals running to/from controller
  input  logic        deassert_we_i,           // deassert we, we are stalled or not active

  output logic        illegal_insn_o,          // illegal instruction encountered
  output logic        ebrk_insn_o,             // trap instruction encountered

  output logic        mret_insn_o,             // return from exception instruction encountered (M)
  output logic        uret_insn_o,             // return from exception instruction encountered (S)
  output logic        dret_insn_o,             // return from debug (M)

  output logic        mret_dec_o,              // return from exception instruction encountered (M) without deassert
  output logic        uret_dec_o,              // return from exception instruction encountered (S) without deassert
  output logic        dret_dec_o,              // return from debug (M) without deassert

  output logic        ecall_insn_o,            // environment call (syscall) instruction encountered
  output logic        wfi_o       ,            // pipeline flush is requested

  output logic        fencei_insn_o,           // fence.i instruction

  output logic        rega_used_o,             // rs1 is used by current instruction
  output logic        regb_used_o,             // rs2 is used by current instruction
  output logic        regc_used_o,             // rs3 is used by current instruction

  output logic [ 0:0] bmask_a_mux_o,           // bit manipulation mask a mux
  output logic [ 1:0] bmask_b_mux_o,           // bit manipulation mask b mux
  output logic        alu_bmask_a_mux_sel_o,   // bit manipulation mask a mux (reg or imm)
  output logic        alu_bmask_b_mux_sel_o,   // bit manipulation mask b mux (reg or imm)

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,           // instruction read from instr memory/cache
  input  logic        illegal_c_insn_i,        // compressed instruction decode failed

  // ALU signals
  output logic        alu_en_o,                // ALU enable
  output alu_opcode_e alu_operator_o, // ALU operation selection
  output logic [2:0]  alu_op_a_mux_sel_o,      // operand a selection: reg value, PC, immediate or zero
  output logic [2:0]  alu_op_b_mux_sel_o,      // operand b selection: reg value or immediate
  output logic [1:0]  alu_op_c_mux_sel_o,      // operand c selection: reg value or jump target
  output logic [1:0]  alu_vec_mode_o,          // selects between 32 bit, 16 bit and 8 bit vectorial modes
  output logic        scalar_replication_o,    // scalar replication enable
  output logic        scalar_replication_c_o,  // scalar replication enable for operand C
  output logic [0:0]  imm_a_mux_sel_o,         // immediate selection for operand a
  output logic [3:0]  imm_b_mux_sel_o,         // immediate selection for operand b
  output logic [1:0]  regc_mux_o,              // register c selection: S3, RD or 0
  output logic        is_clpx_o,               // whether the instruction is complex (pulpv3) or not
  output logic        is_subrot_o,

  // MUL related control signals
  output mul_opcode_e mult_operator_o,         // Multiplication operation selection
  output logic        mult_int_en_o,           // perform integer multiplication
  output logic        mult_dot_en_o,           // perform dot multiplication
  output logic [0:0]  mult_imm_mux_o,          // Multiplication immediate mux selector
  output logic        mult_sel_subword_o,      // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,      // Multiplication in signed mode
  output logic [1:0]  mult_dot_signed_o,       // Dot product in signed mode

  // APU
  output logic                apu_en_o,
  output logic [APU_WOP_CPU-1:0]  apu_op_o,
  output logic [1:0]          apu_lat_o,

  // register file related signals
  output logic        regfile_mem_we_o,        // write enable for regfile
  output logic        regfile_alu_we_o,        // write enable for 2nd regfile port
  output logic        regfile_alu_we_dec_o,    // write enable for 2nd regfile port without deassert
  output logic        regfile_alu_waddr_sel_o, // Select register write address for ALU/MUL operations

  // CSR manipulation
  output logic        csr_access_o,            // access to CSR
  output logic        csr_status_o,            // access to xstatus CSR
  output csr_opcode_e csr_op_o,                // operation to perform on CSR
  input  PrivLvl_t    current_priv_lvl_i,      // The current privilege level

  // LD/ST unit signals
  output logic        data_req_o,              // start transaction to data memory
  output logic        data_we_o,               // data memory write enable
  output logic        prepost_useincr_o,       // when not active bypass the alu result for address calculation
  output logic [1:0]  data_type_o,             // data type on data memory: byte, half word or word
  output logic [1:0]  data_sign_extension_o,   // sign extension on read data from data memory / NaN boxing
  output logic [1:0]  data_reg_offset_o,       // offset in byte inside register for stores
  output logic        data_load_event_o,       // data request is in the special event range

  // Atomic memory access
  output  logic [5:0] atop_o,

  // hwloop signals
  output logic [2:0]  hwlp_we_o,               // write enable for hwloop regs
  output logic        hwlp_target_mux_sel_o,   // selects immediate for hwloop target
  output logic        hwlp_start_mux_sel_o,    // selects hwloop start address input
  output logic        hwlp_cnt_mux_sel_o,      // selects hwloop counter input

  input  logic        debug_mode_i,            // processor is in debug mode
  input  logic        debug_wfi_no_sleep_i,    // do not let WFI cause sleep

  // jump/branches
  output logic [1:0]  ctrl_transfer_insn_in_dec_o,  // control transfer instruction without deassert
  output logic [1:0]  ctrl_transfer_insn_in_id_o,   // control transfer instructio is decoded
  output logic [1:0]  ctrl_transfer_target_mux_sel_o,        // jump target selection

  // HPM related control signals
  input  logic [31:0] mcounteren_i
);

  // write enable/request control
  logic       regfile_mem_we;
  logic       regfile_alu_we;
  logic       data_req;
  logic [2:0] hwlp_we;
  logic       csr_illegal;
  logic [1:0] ctrl_transfer_insn;

  csr_opcode_e csr_op;

  logic       alu_en;
  logic       mult_int_en;
  logic       mult_dot_en;
  logic       apu_en;


  /////////////////////////////////////////////
  //   ____                     _            //
  //  |  _ \  ___  ___ ___   __| | ___ _ __  //
  //  | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  //  | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  |____/ \___|\___\___/ \__,_|\___|_|    //
  //                                         //
  /////////////////////////////////////////////

  always_comb
  begin
    ctrl_transfer_insn          = BRANCH_NONE;
    ctrl_transfer_target_mux_sel_o       = JT_JAL;

    alu_en                      = 1'b1;
    alu_operator_o              = ALU_SLTU;
    alu_op_a_mux_sel_o          = OP_A_REGA_OR_FWD;
    alu_op_b_mux_sel_o          = OP_B_REGB_OR_FWD;
    alu_op_c_mux_sel_o          = OP_C_REGC_OR_FWD;
    alu_vec_mode_o              = VEC_MODE32;
    scalar_replication_o        = 1'b0;
    scalar_replication_c_o      = 1'b0;
    regc_mux_o                  = REGC_ZERO;
    imm_a_mux_sel_o             = IMMA_ZERO;
    imm_b_mux_sel_o             = IMMB_I;

    mult_operator_o             = MUL_I;
    mult_int_en                 = 1'b0;
    mult_dot_en                 = 1'b0;
    mult_imm_mux_o              = MIMM_ZERO;
    mult_signed_mode_o          = 2'b00;
    mult_sel_subword_o          = 1'b0;
    mult_dot_signed_o           = 2'b00;

    apu_en                      = 1'b0;
    apu_op_o                    = '0;
    apu_lat_o                   = '0;

    regfile_mem_we              = 1'b0;
    regfile_alu_we              = 1'b0;
    regfile_alu_waddr_sel_o     = 1'b1;

    prepost_useincr_o           = 1'b1;

    hwlp_we                     = 3'b0;
    hwlp_target_mux_sel_o       = 1'b0;
    hwlp_start_mux_sel_o        = 1'b0;
    hwlp_cnt_mux_sel_o          = 1'b0;

    csr_access_o                = 1'b0;
    csr_status_o                = 1'b0;
    csr_illegal                 = 1'b0;
    csr_op                      = CSR_OP_READ;
    mret_insn_o                 = 1'b0;
    uret_insn_o                 = 1'b0;

    dret_insn_o                 = 1'b0;

    data_we_o                   = 1'b0;
    data_type_o                 = 2'b00;
    data_sign_extension_o       = 2'b00;
    data_reg_offset_o           = 2'b00;
    data_req                    = 1'b0;
    data_load_event_o           = 1'b0;

    atop_o                      = 6'b000000;

    illegal_insn_o              = 1'b0;
    ebrk_insn_o                 = 1'b0;
    ecall_insn_o                = 1'b0;
    wfi_o                       = 1'b0;

    fencei_insn_o               = 1'b0;

    rega_used_o                 = 1'b0;
    regb_used_o                 = 1'b0;
    regc_used_o                 = 1'b0;

    bmask_a_mux_o               = BMASK_A_ZERO;
    bmask_b_mux_o               = BMASK_B_ZERO;
    alu_bmask_a_mux_sel_o       = BMASK_A_IMM;
    alu_bmask_b_mux_sel_o       = BMASK_B_IMM;

    is_clpx_o                   = 1'b0;
    is_subrot_o                 = 1'b0;

    mret_dec_o                  = 1'b0;
    uret_dec_o                  = 1'b0;
    dret_dec_o                  = 1'b0;

    unique case (instr_rdata_i[6:0])

      //////////////////////////////////////
      //      _ _   _ __  __ ____  ____   //
      //     | | | | |  \/  |  _ \/ ___|  //
      //  _  | | | | | |\/| | |_) \___ \  //
      // | |_| | |_| | |  | |  __/ ___) | //
      //  \___/ \___/|_|  |_|_|   |____/  //
      //                                  //
      //////////////////////////////////////

      OPCODE_JAL: begin   // Jump and Link
        ctrl_transfer_target_mux_sel_o = JT_JAL;
        ctrl_transfer_insn    = BRANCH_JAL;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= PC + UJ imm)
      end

      OPCODE_JALR: begin  // Jump and Link Register
        ctrl_transfer_target_mux_sel_o = JT_JALR;
        ctrl_transfer_insn    = BRANCH_JALR;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= RS1 + I imm)
        rega_used_o         = 1'b1;

        if (instr_rdata_i[14:12] != 3'b0) begin
          ctrl_transfer_insn = BRANCH_NONE;
          regfile_alu_we     = 1'b0;
          illegal_insn_o     = 1'b1;
        end
      end

      OPCODE_BRANCH: begin // Branch
        ctrl_transfer_target_mux_sel_o = JT_COND;
        ctrl_transfer_insn    = BRANCH_COND;
        alu_op_c_mux_sel_o    = OP_C_JT;
        rega_used_o           = 1'b1;
        regb_used_o           = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator_o = ALU_EQ;
          3'b001: alu_operator_o = ALU_NE;
          3'b100: alu_operator_o = ALU_LTS;
          3'b101: alu_operator_o = ALU_GES;
          3'b110: alu_operator_o = ALU_LTU;
          3'b111: alu_operator_o = ALU_GEU;
          3'b010: begin // p.beqimm
            if (PULP_XPULP) begin
              alu_operator_o      = ALU_EQ;
              regb_used_o         = 1'b0;
              alu_op_b_mux_sel_o  = OP_B_IMM;
              imm_b_mux_sel_o     = IMMB_BI;
            end else begin
              illegal_insn_o = 1'b1;
            end
          end
          3'b011: begin // p.bneimm
            if (PULP_XPULP) begin
              alu_operator_o      = ALU_NE;
              regb_used_o         = 1'b0;
              alu_op_b_mux_sel_o  = OP_B_IMM;
              imm_b_mux_sel_o     = IMMB_BI;
            end else begin
              illegal_insn_o = 1'b1;
            end
          end
        endcase
      end


      //////////////////////////////////
      //  _     ____    ______ _____  //
      // | |   |  _ \  / / ___|_   _| //
      // | |   | | | |/ /\___ \ | |   //
      // | |___| |_| / /  ___) || |   //
      // |_____|____/_/  |____/ |_|   //
      //                              //
      //////////////////////////////////

      OPCODE_STORE,
      OPCODE_STORE_POST: begin
        if (PULP_XPULP || (instr_rdata_i[6:0] == OPCODE_STORE)) begin
          data_req       = 1'b1;
          data_we_o      = 1'b1;
          rega_used_o    = 1'b1;
          regb_used_o    = 1'b1;
          alu_operator_o = ALU_ADD;
          // pass write data through ALU operand c
          alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;

          // post-increment setup
          if (instr_rdata_i[6:0] == OPCODE_STORE_POST) begin
            prepost_useincr_o       = 1'b0;
            regfile_alu_waddr_sel_o = 1'b0;
            regfile_alu_we          = 1'b1;
          end

          if (instr_rdata_i[14] == 1'b0) begin
            // offset from immediate
            imm_b_mux_sel_o     = IMMB_S;
            alu_op_b_mux_sel_o  = OP_B_IMM;
          end else begin
            if (PULP_XPULP) begin
              // offset from register
              regc_used_o        = 1'b1;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
              regc_mux_o         = REGC_RD;
            end else begin
              illegal_insn_o = 1'b1;
            end
          end

          // store size
          unique case (instr_rdata_i[13:12])
            2'b00: data_type_o = 2'b10; // SB
            2'b01: data_type_o = 2'b01; // SH
            2'b10: data_type_o = 2'b00; // SW
            default: begin
              data_req       = 1'b0;
              data_we_o      = 1'b0;
              illegal_insn_o = 1'b1;
            end
          endcase
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_LOAD,
      OPCODE_LOAD_POST: begin
        if (PULP_XPULP || (instr_rdata_i[6:0] == OPCODE_LOAD)) begin
          data_req        = 1'b1;
          regfile_mem_we  = 1'b1;
          rega_used_o     = 1'b1;
          data_type_o     = 2'b00;
          // offset from immediate
          alu_operator_o      = ALU_ADD;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMMB_I;

          // post-increment setup
          if (instr_rdata_i[6:0] == OPCODE_LOAD_POST) begin
            prepost_useincr_o       = 1'b0;
            regfile_alu_waddr_sel_o = 1'b0;
            regfile_alu_we          = 1'b1;
          end

          // sign/zero extension
          data_sign_extension_o = {1'b0,~instr_rdata_i[14]};

          // load size
          unique case (instr_rdata_i[13:12])
            2'b00:   data_type_o = 2'b10; // LB
            2'b01:   data_type_o = 2'b01; // LH
            2'b10:   data_type_o = 2'b00; // LW
            default: data_type_o = 2'b00; // illegal or reg-reg
          endcase

          // reg-reg load (different encoding)
          if (instr_rdata_i[14:12] == 3'b111) begin
            if (PULP_XPULP) begin
              // offset from RS2
              regb_used_o        = 1'b1;
              alu_op_b_mux_sel_o = OP_B_REGB_OR_FWD;

              // sign/zero extension
              data_sign_extension_o = {1'b0, ~instr_rdata_i[30]};

              // load size
              unique case (instr_rdata_i[31:25])
                7'b0000_000,
                7'b0100_000: data_type_o = 2'b10; // LB, LBU
                7'b0001_000,
                7'b0101_000: data_type_o = 2'b01; // LH, LHU
                7'b0010_000: data_type_o = 2'b00; // LW
                default: begin
                  illegal_insn_o = 1'b1;
                end
              endcase
            end else begin
              illegal_insn_o = 1'b1;
            end
          end

          // special p.elw (event load)
          if (instr_rdata_i[14:12] == 3'b110) begin
            if (PULP_CLUSTER && (instr_rdata_i[6:0] == OPCODE_LOAD)) begin
              data_load_event_o = 1'b1;
            end else begin
              // p.elw only valid for PULP_CLUSTER = 1; p.elw with post increment does not exist
              illegal_insn_o = 1'b1;
            end
          end

          if (instr_rdata_i[14:12] == 3'b011) begin
            // LD -> RV64 only
            illegal_insn_o = 1'b1;
          end
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_AMO: begin
        if (A_EXTENSION) begin : decode_amo
          if (instr_rdata_i[14:12] == 3'b010) begin // RV32A Extension (word)
            data_req          = 1'b1;
            data_type_o       = 2'b00;
            rega_used_o       = 1'b1;
            regb_used_o       = 1'b1;
            regfile_mem_we    = 1'b1;
            prepost_useincr_o = 1'b0; // only use alu_operand_a as address (not a+b)
            alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;

            data_sign_extension_o = 1'b1;

            // Apply AMO instruction at `atop_o`.
            atop_o = {1'b1, instr_rdata_i[31:27]};

            unique case (instr_rdata_i[31:27])
              AMO_LR: begin
                data_we_o = 1'b0;
              end
              AMO_SC,
              AMO_SWAP,
              AMO_ADD,
              AMO_XOR,
              AMO_AND,
              AMO_OR,
              AMO_MIN,
              AMO_MAX,
              AMO_MINU,
              AMO_MAXU: begin
                data_we_o = 1'b1;
                alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD; // pass write data through ALU operand c
              end
              default : illegal_insn_o = 1'b1;
            endcase
          end
          else begin
            illegal_insn_o = 1'b1;
          end
        end else begin : no_decode_amo
          illegal_insn_o = 1'b1;
        end
      end


      //////////////////////////
      //     _    _    _   _  //
      //    / \  | |  | | | | //
      //   / _ \ | |  | | | | //
      //  / ___ \| |__| |_| | //
      // /_/   \_\_____\___/  //
      //                      //
      //////////////////////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMMA_ZERO;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_OPIMM: begin // Register-Immediate ALU Operations
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_I;
        regfile_alu_we      = 1'b1;
        rega_used_o         = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLTS; // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator_o = ALU_SLL;  // Shift Left Logical by Immediate
            if (instr_rdata_i[31:25] != 7'b0)
              illegal_insn_o = 1'b1;
          end

          3'b101: begin
            if (instr_rdata_i[31:25] == 7'b0)
              alu_operator_o = ALU_SRL;  // Shift Right Logical by Immediate
            else if (instr_rdata_i[31:25] == 7'b010_0000)
              alu_operator_o = ALU_SRA;  // Shift Right Arithmetically by Immediate
            else
              illegal_insn_o = 1'b1;
          end


        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation

        // PREFIX 11
        if (instr_rdata_i[31:30] == 2'b11) begin
          if (PULP_XPULP) begin
            //////////////////////////////
            // IMMEDIATE BIT-MANIPULATION
            //////////////////////////////

            regfile_alu_we = 1'b1;
            rega_used_o    = 1'b1;

            // bit-manipulation instructions
            bmask_a_mux_o       = BMASK_A_S3;
            bmask_b_mux_o       = BMASK_B_S2;
            alu_op_b_mux_sel_o  = OP_B_IMM;

            unique case (instr_rdata_i[14:12])
              3'b000: begin
                alu_operator_o  = ALU_BEXT;
                imm_b_mux_sel_o = IMMB_S2;
                bmask_b_mux_o   = BMASK_B_ZERO;
              end
              3'b001: begin
                alu_operator_o  = ALU_BEXTU;
                imm_b_mux_sel_o = IMMB_S2;
                bmask_b_mux_o   = BMASK_B_ZERO;
              end
              3'b010: begin
                alu_operator_o  = ALU_BINS;
                imm_b_mux_sel_o = IMMB_S2;
                regc_used_o     = 1'b1;
                regc_mux_o      = REGC_RD;
              end
              3'b011: begin
                alu_operator_o = ALU_BCLR;
              end
              3'b100: begin
                alu_operator_o = ALU_BSET;
              end
              3'b101: begin
                alu_operator_o        = ALU_BREV;
                // Enable write back to RD
                regc_used_o           = 1'b1;
                regc_mux_o            = REGC_RD;
                // Extract the source register on operand a
                imm_b_mux_sel_o       = IMMB_S2;
                // Map the radix to bmask_a immediate
                alu_bmask_a_mux_sel_o = BMASK_A_IMM;
              end
              default: illegal_insn_o = 1'b1;
            endcase
          end else begin
            illegal_insn_o = 1'b1;
          end
        end

        // PREFIX 10
        else if (instr_rdata_i[31:30] == 2'b10) begin
          //////////////////////////////
          // REGISTER BIT-MANIPULATION
          //////////////////////////////
          if (instr_rdata_i[29:25]==5'b00000) begin
            if (PULP_XPULP) begin
              regfile_alu_we = 1'b1;
              rega_used_o    = 1'b1;

              bmask_a_mux_o       = BMASK_A_S3;
              bmask_b_mux_o       = BMASK_B_S2;
              alu_op_b_mux_sel_o  = OP_B_IMM;

              unique case (instr_rdata_i[14:12])
                3'b000: begin
                  alu_operator_o  = ALU_BEXT;
                  imm_b_mux_sel_o = IMMB_S2;
                  bmask_b_mux_o   = BMASK_B_ZERO;
                  //register variant
                  alu_op_b_mux_sel_o     = OP_B_BMASK;
                  alu_bmask_a_mux_sel_o  = BMASK_A_REG;
                  regb_used_o            = 1'b1;
                end
                3'b001: begin
                  alu_operator_o  = ALU_BEXTU;
                  imm_b_mux_sel_o = IMMB_S2;
                  bmask_b_mux_o   = BMASK_B_ZERO;
                  //register variant
                  alu_op_b_mux_sel_o     = OP_B_BMASK;
                  alu_bmask_a_mux_sel_o  = BMASK_A_REG;
                  regb_used_o            = 1'b1;
                end
                3'b010: begin
                  alu_operator_o      = ALU_BINS;
                  imm_b_mux_sel_o     = IMMB_S2;
                  regc_used_o         = 1'b1;
                  regc_mux_o          = REGC_RD;
                  //register variant
                  alu_op_b_mux_sel_o     = OP_B_BMASK;
                  alu_bmask_a_mux_sel_o  = BMASK_A_REG;
                  alu_bmask_b_mux_sel_o  = BMASK_B_REG;
                  regb_used_o            = 1'b1;
                end
                3'b011: begin
                  alu_operator_o = ALU_BCLR;
                  //register variant
                  regb_used_o            = 1'b1;
                  alu_bmask_a_mux_sel_o  = BMASK_A_REG;
                  alu_bmask_b_mux_sel_o  = BMASK_B_REG;
                end
                3'b100: begin
                  alu_operator_o = ALU_BSET;
                  //register variant
                  regb_used_o            = 1'b1;
                  alu_bmask_a_mux_sel_o  = BMASK_A_REG;
                  alu_bmask_b_mux_sel_o  = BMASK_B_REG;
                end
                default: illegal_insn_o = 1'b1;
              endcase
            end else begin
              illegal_insn_o = 1'b1;
            end

          ///////////////////////
          // VECTORIAL FLOAT OPS
          ///////////////////////
          end else begin
            illegal_insn_o = 1'b1;
          end // Vectorial Float Ops

        end  // prefix 10

        // PREFIX 00/01
        else begin
          // non bit-manipulation instructions
          regfile_alu_we = 1'b1;
          rega_used_o    = 1'b1;

          if (~instr_rdata_i[28]) regb_used_o = 1'b1;

          unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
            // RV32I ALU operations
            {6'b00_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {6'b10_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {6'b00_0000, 3'b010}: alu_operator_o = ALU_SLTS;  // Set Lower Than
            {6'b00_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {6'b00_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {6'b00_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {6'b00_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {6'b00_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {6'b00_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {6'b10_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              alu_en          = 1'b0;
              mult_int_en     = 1'b1;
              mult_operator_o = MUL_MAC32;
              regc_mux_o      = REGC_ZERO;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              alu_en             = 1'b0;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b11;
              mult_int_en        = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              alu_en             = 1'b0;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b01;
              mult_int_en        = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              alu_en             = 1'b0;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b00;
              mult_int_en        = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b100}: begin // div
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_DIV;
            end
            {6'b00_0001, 3'b101}: begin // divu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_DIVU;
            end
            {6'b00_0001, 3'b110}: begin // rem
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_REM;
            end
            {6'b00_0001, 3'b111}: begin // remu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_REMU;
            end

            // PULP specific instructions
            {6'b10_0001, 3'b000}: begin         // p.mac
              if (PULP_XPULP) begin
                alu_en          = 1'b0;
                regc_used_o     = 1'b1;
                regc_mux_o      = REGC_RD;
                mult_int_en     = 1'b1;
                mult_operator_o = MUL_MAC32;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b10_0001, 3'b001}: begin         // p.msu
              if (PULP_XPULP) begin
                alu_en          = 1'b0;
                regc_used_o     = 1'b1;
                regc_mux_o      = REGC_RD;
                mult_int_en     = 1'b1;
                mult_operator_o = MUL_MSU32;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b010}: begin         // Set Lower Equal Than - p.slet
              if (PULP_XPULP) begin
                alu_operator_o = ALU_SLETS;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b011}: begin         // Set Lower Equal Than Unsigned; p.sletu
              if (PULP_XPULP) begin
                alu_operator_o = ALU_SLETU;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b100}: begin         // Min - p.min
              if (PULP_XPULP) begin
                alu_operator_o = ALU_MIN;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b101}: begin         // Min Unsigned - p.minu
              if (PULP_XPULP) begin
                alu_operator_o = ALU_MINU;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b110}: begin         // Max - p.max
              if (PULP_XPULP) begin
                alu_operator_o = ALU_MAX;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b111}: begin         // Max Unsigned - p.maxu
              if (PULP_XPULP) begin
                alu_operator_o = ALU_MAXU;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0100, 3'b101}: begin         // Rotate Right - p.ror
              if (PULP_XPULP) begin
                alu_operator_o = ALU_ROR;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end

            // PULP specific instructions using only one source register

            {6'b00_1000, 3'b000}: begin         // Find First 1 - p.ff1
              if (PULP_XPULP) begin
                alu_operator_o = ALU_FF1;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b001}: begin         // Find Last 1 - p.fl1
              if (PULP_XPULP) begin
                alu_operator_o = ALU_FL1;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b010}: begin         // Count Leading Bits - p.clb
              if (PULP_XPULP) begin
                alu_operator_o = ALU_CLB;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b011}: begin         // Count set bits (popcount) - p.cnt
              if (PULP_XPULP) begin
                alu_operator_o = ALU_CNT;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b100}: begin         // Sign-extend Halfword - p.exths
              if (PULP_XPULP) begin
                alu_operator_o = ALU_EXTS;
                alu_vec_mode_o = VEC_MODE16;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b101}: begin         // Zero-extend Halfword - p.exthz
              if (PULP_XPULP) begin
                alu_operator_o = ALU_EXT;
                alu_vec_mode_o = VEC_MODE16;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b110}: begin         // Sign-extend Byte - p.extbs
              if (PULP_XPULP) begin
                alu_operator_o = ALU_EXTS;
                alu_vec_mode_o = VEC_MODE8;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1000, 3'b111}: begin         // Zero-extend Byte - p.extbz
              if (PULP_XPULP) begin
                alu_operator_o = ALU_EXT;
                alu_vec_mode_o = VEC_MODE8;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_0010, 3'b000}: begin         // p.abs
              if (PULP_XPULP) begin
                alu_operator_o = ALU_ABS;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1010, 3'b001}: begin         // p.clip
              if (PULP_XPULP) begin
                alu_operator_o     = ALU_CLIP;
                alu_op_b_mux_sel_o = OP_B_IMM;
                imm_b_mux_sel_o    = IMMB_CLIP;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1010, 3'b010}: begin         // p.clipu
              if (PULP_XPULP) begin
                alu_operator_o     = ALU_CLIPU;
                alu_op_b_mux_sel_o = OP_B_IMM;
                imm_b_mux_sel_o    = IMMB_CLIP;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1010, 3'b101}: begin         // p.clipr
              if (PULP_XPULP) begin
                alu_operator_o     = ALU_CLIP;
                regb_used_o        = 1'b1;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end
            {6'b00_1010, 3'b110}: begin         // p.clipur
              if (PULP_XPULP) begin
                alu_operator_o     = ALU_CLIPU;
                regb_used_o        = 1'b1;
              end else begin
                illegal_insn_o = 1'b1;
              end
            end

            default: begin
              illegal_insn_o = 1'b1;
            end
          endcase
        end
      end

      ////////////////////////////
      //  ______ _____  _    _  //
      // |  ____|  __ \| |  | | //
      // | |__  | |__) | |  | | //
      // |  __| |  ___/| |  | | //
      // | |    | |    | |__| | //
      // |_|    |_|     \____/  //
      //                        //
      ////////////////////////////

      // floating point arithmetic
      OPCODE_OP_FP: begin
          illegal_insn_o = 1'b1;
      end

      // floating point fused arithmetic
      OPCODE_OP_FMADD,
      OPCODE_OP_FMSUB,
      OPCODE_OP_FNMSUB,
      OPCODE_OP_FNMADD : begin
          illegal_insn_o = 1'b1;
      end

      OPCODE_STORE_FP: begin
          illegal_insn_o = 1'b1;
          data_we_o = 1'b0;
          data_req  = 1'b0;
      end

      OPCODE_LOAD_FP: begin
          illegal_insn_o = 1'b1;
      end

      OPCODE_PULP_OP: begin  // PULP specific ALU instructions with three source operands
        if (PULP_XPULP) begin
          regfile_alu_we = 1'b1;
          rega_used_o    = 1'b1;
          regb_used_o    = 1'b1;

          case (instr_rdata_i[13:12])
            2'b00: begin // multiply with subword selection
              alu_en             = 1'b0;

              mult_sel_subword_o = instr_rdata_i[30];
              mult_signed_mode_o = {2{instr_rdata_i[31]}};

              mult_imm_mux_o = MIMM_S3;
              regc_mux_o     = REGC_ZERO;
              mult_int_en    = 1'b1;

              if (instr_rdata_i[14])
                mult_operator_o = MUL_IR;
              else
                mult_operator_o = MUL_I;
            end

            2'b01: begin // MAC with subword selection
              alu_en             = 1'b0;

              mult_sel_subword_o = instr_rdata_i[30];
              mult_signed_mode_o = {2{instr_rdata_i[31]}};

              regc_used_o     = 1'b1;
              regc_mux_o      = REGC_RD;
              mult_imm_mux_o  = MIMM_S3;
              mult_int_en     = 1'b1;

              if (instr_rdata_i[14])
                mult_operator_o = MUL_IR;
              else
                mult_operator_o = MUL_I;
            end

            2'b10: begin // add with normalization and rounding
              // decide between using unsigned and rounding, and combinations
              // thereof
              case ({instr_rdata_i[31],instr_rdata_i[14]})
                2'b00: alu_operator_o = ALU_ADD;
                2'b01: alu_operator_o = ALU_ADDR;
                2'b10: alu_operator_o = ALU_ADDU;
                2'b11: alu_operator_o = ALU_ADDUR;
              endcase

              bmask_a_mux_o = BMASK_A_ZERO;
              bmask_b_mux_o = BMASK_B_S3;

              if (instr_rdata_i[30]) begin
                //register variant
                regc_used_o            = 1'b1;
                regc_mux_o             = REGC_RD;
                alu_bmask_b_mux_sel_o  = BMASK_B_REG;
                alu_op_a_mux_sel_o     = OP_A_REGC_OR_FWD;
                alu_op_b_mux_sel_o     = OP_B_REGA_OR_FWD;
              end

            end

            2'b11: begin // sub with normalization and rounding
              // decide between using unsigned and rounding, and combinations
              // thereof
              case ({instr_rdata_i[31],instr_rdata_i[14]})
                2'b00: alu_operator_o = ALU_SUB;
                2'b01: alu_operator_o = ALU_SUBR;
                2'b10: alu_operator_o = ALU_SUBU;
                2'b11: alu_operator_o = ALU_SUBUR;
              endcase

              bmask_a_mux_o = BMASK_A_ZERO;
              bmask_b_mux_o = BMASK_B_S3;

              if (instr_rdata_i[30]) begin
                //register variant
                regc_used_o            = 1'b1;
                regc_mux_o             = REGC_RD;
                alu_bmask_b_mux_sel_o  = BMASK_B_REG;
                alu_op_a_mux_sel_o     = OP_A_REGC_OR_FWD;
                alu_op_b_mux_sel_o     = OP_B_REGA_OR_FWD;
              end

            end
          endcase
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_VECOP: begin
        if (PULP_XPULP) begin
          regfile_alu_we      = 1'b1;
          rega_used_o         = 1'b1;
          imm_b_mux_sel_o     = IMMB_VS;

          // vector size
          if (instr_rdata_i[12]) begin
            alu_vec_mode_o  = VEC_MODE8;
            mult_operator_o = MUL_DOT8;
          end else begin
            alu_vec_mode_o = VEC_MODE16;
            mult_operator_o = MUL_DOT16;
          end

          // distinguish normal vector, sc and sci modes
          if (instr_rdata_i[14]) begin
            scalar_replication_o = 1'b1;

            if (instr_rdata_i[13]) begin
              // immediate scalar replication, .sci
              alu_op_b_mux_sel_o = OP_B_IMM;
            end else begin
              // register scalar replication, .sc
              regb_used_o = 1'b1;
            end
          end else begin
            // normal register use
            regb_used_o = 1'b1;
          end

          // now decode the instruction
          unique case (instr_rdata_i[31:26])
            6'b00000_0: begin alu_operator_o = ALU_ADD;  imm_b_mux_sel_o = IMMB_VS;  end // pv.add
            6'b00001_0: begin alu_operator_o = ALU_SUB;  imm_b_mux_sel_o = IMMB_VS;  end // pv.sub
            6'b00010_0: begin alu_operator_o = ALU_ADD;  imm_b_mux_sel_o = IMMB_VS; bmask_b_mux_o = BMASK_B_ONE;  end // pv.avg
            6'b00011_0: begin alu_operator_o = ALU_ADDU; imm_b_mux_sel_o = IMMB_VU; bmask_b_mux_o = BMASK_B_ONE;  end // pv.avgu
            6'b00100_0: begin alu_operator_o = ALU_MIN;  imm_b_mux_sel_o = IMMB_VS;  end // pv.min
            6'b00101_0: begin alu_operator_o = ALU_MINU; imm_b_mux_sel_o = IMMB_VU;  end // pv.minu
            6'b00110_0: begin alu_operator_o = ALU_MAX;  imm_b_mux_sel_o = IMMB_VS;  end // pv.max
            6'b00111_0: begin alu_operator_o = ALU_MAXU; imm_b_mux_sel_o = IMMB_VU;  end // pv.maxu
            6'b01000_0: begin alu_operator_o = ALU_SRL;  imm_b_mux_sel_o = IMMB_VS;  end // pv.srl
            6'b01001_0: begin alu_operator_o = ALU_SRA;  imm_b_mux_sel_o = IMMB_VS;  end // pv.sra
            6'b01010_0: begin alu_operator_o = ALU_SLL;  imm_b_mux_sel_o = IMMB_VS;  end // pv.sll
            6'b01011_0: begin alu_operator_o = ALU_OR;   imm_b_mux_sel_o = IMMB_VS;  end // pv.or
            6'b01100_0: begin alu_operator_o = ALU_XOR;  imm_b_mux_sel_o = IMMB_VS;  end // pv.xor
            6'b01101_0: begin alu_operator_o = ALU_AND;  imm_b_mux_sel_o = IMMB_VS;  end // pv.and
            6'b01110_0: begin alu_operator_o = ALU_ABS;  imm_b_mux_sel_o = IMMB_VS;  end // pv.abs

            // shuffle/pack
            6'b11101_0,       // pv.shuffleI1
            6'b11110_0,       // pv.shuffleI2
            6'b11111_0,       // pv.shuffleI3
            6'b11000_0: begin // pv.shuffle, pv.shuffleI0
              alu_operator_o       = ALU_SHUF;
              imm_b_mux_sel_o      = IMMB_SHUF;
              regb_used_o          = 1'b1;
              scalar_replication_o = 1'b0;
            end
            6'b11001_0: begin // pv.shuffle2
              alu_operator_o       = ALU_SHUF2;
              regb_used_o          = 1'b1;
              regc_used_o          = 1'b1;
              regc_mux_o           = REGC_RD;
              scalar_replication_o = 1'b0;
            end
            6'b11010_0: begin // pv.pack
              alu_operator_o = instr_rdata_i[25] ? ALU_PCKHI : ALU_PCKLO;
              regb_used_o    = 1'b1;
            end
            6'b11011_0: begin // pv.packhi
              alu_operator_o = ALU_PCKHI;
              regb_used_o    = 1'b1;
              regc_used_o    = 1'b1;
              regc_mux_o     = REGC_RD;
            end
            6'b11100_0: begin // pv.packlo
              alu_operator_o = ALU_PCKLO;
              regb_used_o    = 1'b1;
              regc_used_o    = 1'b1;
              regc_mux_o     = REGC_RD;
            end
            6'b01111_0: begin // pv.extract
              alu_operator_o = ALU_EXTS;
            end
            6'b10010_0: begin // pv.extractu
              alu_operator_o = ALU_EXT;
            end
            6'b10110_0: begin // pv.insert
              alu_operator_o     = ALU_INS;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_RD;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
            end
            6'b10000_0: begin // pv.dotup
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b00;
              imm_b_mux_sel_o   = IMMB_VU;
            end
            6'b10001_0: begin // pv.dotusp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b01;
            end
            6'b10011_0: begin // pv.dotsp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b11;
            end
            6'b10100_0: begin // pv.sdotup
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b00;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
              imm_b_mux_sel_o   = IMMB_VU;
            end
            6'b10101_0: begin // pv.sdotusp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b01;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
            end
            6'b10111_0: begin // pv.sdotsp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b11;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
            end

            /*  COMPLEX INSTRUCTIONS */

            6'b01010_1: begin // pc.clpxmul.{r,i}.{/,div2,div4,div8}
              alu_en               = 1'b0;
              mult_dot_en          = 1'b1;
              mult_dot_signed_o    = 2'b11;
              is_clpx_o            = 1'b1;
              regc_used_o          = 1'b1;
              regc_mux_o           = REGC_RD;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              illegal_insn_o       = instr_rdata_i[12];
            end

            6'b01101_1: begin // pv.subrotmj.{/,div2,div4,div8}
              alu_operator_o       = ALU_SUB;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              is_subrot_o          = 1'b1;
              illegal_insn_o       = instr_rdata_i[12];
            end

            6'b01011_1: begin // pv.cplxconj
              alu_operator_o       = ALU_ABS;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              regb_used_o          = 1'b0;
              illegal_insn_o       = instr_rdata_i[12] || (instr_rdata_i[24:20]!='0);
            end

            6'b01110_1: begin // pv.add.{div2,div4,div8}
              alu_operator_o       = ALU_ADD;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              illegal_insn_o       = instr_rdata_i[12];
            end

            6'b01100_1: begin // pv.sub.{div2,div4,div8}
              alu_operator_o       = ALU_SUB;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              illegal_insn_o       = instr_rdata_i[12];
            end

            // comparisons, always have bit 26 set
            6'b00000_1: begin alu_operator_o = ALU_EQ;  imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpeq
            6'b00001_1: begin alu_operator_o = ALU_NE;  imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpne
            6'b00010_1: begin alu_operator_o = ALU_GTS; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpgt
            6'b00011_1: begin alu_operator_o = ALU_GES; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpge
            6'b00100_1: begin alu_operator_o = ALU_LTS; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmplt
            6'b00101_1: begin alu_operator_o = ALU_LES; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmple
            6'b00110_1: begin alu_operator_o = ALU_GTU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpgtu
            6'b00111_1: begin alu_operator_o = ALU_GEU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpgeu
            6'b01000_1: begin alu_operator_o = ALU_LTU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpltu
            6'b01001_1: begin alu_operator_o = ALU_LEU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpleu

            default: illegal_insn_o = 1'b1;
          endcase
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      ////////////////////////////////////////////////
      //  ____  ____  _____ ____ ___    _    _      //
      // / ___||  _ \| ____/ ___|_ _|  / \  | |     //
      // \___ \| |_) |  _|| |    | |  / _ \ | |     //
      //  ___) |  __/| |__| |___ | | / ___ \| |___  //
      // |____/|_|   |_____\____|___/_/   \_\_____| //
      //                                            //
      ////////////////////////////////////////////////

      OPCODE_FENCE: begin
        unique case (instr_rdata_i[14:12])
          3'b000: begin // FENCE (FENCE.I instead, a bit more conservative)
            // flush pipeline
            fencei_insn_o = 1'b1;
          end

          3'b001: begin // FENCE.I
            // flush prefetch buffer, flush pipeline
            fencei_insn_o = 1'b1;
          end

          default: begin
            illegal_insn_o =  1'b1;
          end
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr_rdata_i[14:12] == 3'b000)
        begin
          // non CSR related SYSTEM instructions
          if ( {instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0)
          begin
            unique case (instr_rdata_i[31:20])
              12'h000:  // ECALL
              begin
                // environment (system) call
                ecall_insn_o  = 1'b1;
              end

              12'h001:  // ebreak
              begin
                // debugger trap
                ebrk_insn_o = 1'b1;
              end

              12'h302:  // mret
              begin
                illegal_insn_o = (PULP_SECURE) ? current_priv_lvl_i != PRIV_LVL_M : 1'b0;
                mret_insn_o    = ~illegal_insn_o;
                mret_dec_o     = 1'b1;
              end

              12'h002:  // uret
              begin
                illegal_insn_o = (PULP_SECURE) ? 1'b0 : 1'b1;
                uret_insn_o    = ~illegal_insn_o;
                uret_dec_o     = 1'b1;
              end

              12'h7b2:  // dret
              begin
                illegal_insn_o = !debug_mode_i;
                dret_insn_o    =  debug_mode_i;
                dret_dec_o     =  1'b1;
              end

              12'h105:  // wfi
              begin
                wfi_o = 1'b1;
                if (debug_wfi_no_sleep_i) begin
                  // Treat as NOP (do not cause sleep mode entry)
                  // Using decoding similar to ADDI, but without register reads/writes, i.e.
                  // keep regfile_alu_we = 0, rega_used_o = 0
                  alu_op_b_mux_sel_o = OP_B_IMM;
                  imm_b_mux_sel_o = IMMB_I;
                  alu_operator_o = ALU_ADD;
                end
              end

              default:
              begin
                illegal_insn_o = 1'b1;
              end
            endcase
          end else illegal_insn_o = 1'b1;
        end
        else
        begin
          // instruction to read/modify CSR
          csr_access_o        = 1'b1;
          regfile_alu_we      = 1'b1;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_a_mux_sel_o     = IMMA_Z;
          imm_b_mux_sel_o     = IMMB_I;    // CSR address is encoded in I imm

          if (instr_rdata_i[14] == 1'b1) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            rega_used_o        = 1'b1;
            alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;
          end

          // instr_rdata_i[19:14] = rs or immediate value
          //   if set or clear with rs==x0 or imm==0,
          //   then do not perform a write action
          unique case (instr_rdata_i[13:12])
            2'b01:   csr_op   = CSR_OP_WRITE;
            2'b10:   csr_op   = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_SET;
            2'b11:   csr_op   = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_CLEAR;
            default: csr_illegal = 1'b1;
          endcase

          if (instr_rdata_i[29:28] > current_priv_lvl_i) begin
            // No access to higher privilege CSR
            csr_illegal = 1'b1;
          end

          // Determine if CSR access is illegal
          case (instr_rdata_i[31:20])
            // Floating point
            CSR_FFLAGS,
              CSR_FRM,
              CSR_FCSR :
                csr_illegal = 1'b1;

            //  Writes to read only CSRs results in illegal instruction
            CSR_MVENDORID,
              CSR_MARCHID,
              CSR_MIMPID,
              CSR_MHARTID :
                if(csr_op != CSR_OP_READ) csr_illegal = 1'b1;

            // These are valid CSR registers
            CSR_MSTATUS,
              CSR_MEPC,
              CSR_MTVEC,
              CSR_MCAUSE :
                // Not illegal, but treat as status CSR for side effect handling
                csr_status_o = 1'b1;

            // These are valid CSR registers
            CSR_MISA,
              CSR_MIE,
              CSR_MSCRATCH,
              CSR_MTVAL,
              CSR_MIP :
                ; // do nothing, not illegal

            // Hardware Performance Monitor
            CSR_MCYCLE,
              CSR_MINSTRET,
              CSR_MHPMCOUNTER3,
              CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
              CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
              CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
              CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
              CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
              CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
              CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
              CSR_MCYCLEH,
              CSR_MINSTRETH,
              CSR_MHPMCOUNTER3H,
              CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
              CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
              CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
              CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
              CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
              CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
              CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
              CSR_MCOUNTINHIBIT,
              CSR_MHPMEVENT3,
              CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
              CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
              CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
              CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
              CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
              CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
              CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31 :
                // Not illegal, but treat as status CSR to get accurate counts
                csr_status_o = 1'b1;

            // Hardware Performance Monitor (unprivileged read-only mirror CSRs)
            CSR_CYCLE,
              CSR_INSTRET,
              CSR_HPMCOUNTER3,
              CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
              CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
              CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
              CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
              CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
              CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
              CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31,
              CSR_CYCLEH,
              CSR_INSTRETH,
              CSR_HPMCOUNTER3H,
              CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
              CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
              CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
              CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
              CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
              CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
              CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H :
                // Read-only and readable from user mode only if the bit of mcounteren is set
                if((csr_op != CSR_OP_READ) || (PULP_SECURE && (current_priv_lvl_i != PRIV_LVL_M) && !mcounteren_i[instr_rdata_i[24:20]])) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            // This register only exists in user mode
            CSR_MCOUNTEREN :
              if(!PULP_SECURE) begin
                csr_illegal = 1'b1;
              end else begin
                csr_status_o = 1'b1;
              end

            // Debug register access
            CSR_DCSR,
              CSR_DPC,
              CSR_DSCRATCH0,
              CSR_DSCRATCH1 :
                if(!debug_mode_i) begin
                  csr_illegal = 1'b1;
              end else begin
                csr_status_o = 1'b1;
              end

            // Debug Trigger register access
            CSR_TSELECT,
              CSR_TDATA1,
              CSR_TDATA2,
              CSR_TDATA3,
              CSR_TINFO,
              CSR_MCONTEXT,
              CSR_SCONTEXT :
                if(DEBUG_TRIGGER_EN != 1)
                  csr_illegal = 1'b1;

            // Hardware Loop register, UHARTID access
            CSR_LPSTART0,
              CSR_LPEND0,
              CSR_LPCOUNT0,
              CSR_LPSTART1,
              CSR_LPEND1,
              CSR_LPCOUNT1,
              CSR_UHARTID :
                if(!PULP_XPULP) csr_illegal = 1'b1;

            // PRIVLV access
            CSR_PRIVLV :
              if(!PULP_XPULP) begin
                csr_illegal = 1'b1;
              end else begin
                csr_status_o = 1'b1;
              end

            // PMP register access
            CSR_PMPCFG0,
              CSR_PMPCFG1,
              CSR_PMPCFG2,
              CSR_PMPCFG3,
              CSR_PMPADDR0,
              CSR_PMPADDR1,
              CSR_PMPADDR2,
              CSR_PMPADDR3,
              CSR_PMPADDR4,
              CSR_PMPADDR5,
              CSR_PMPADDR6,
              CSR_PMPADDR7,
              CSR_PMPADDR8,
              CSR_PMPADDR9,
              CSR_PMPADDR10,
              CSR_PMPADDR11,
              CSR_PMPADDR12,
              CSR_PMPADDR13,
              CSR_PMPADDR14,
              CSR_PMPADDR15 :
                if(!USE_PMP) csr_illegal = 1'b1;

            // User register access
            CSR_USTATUS,
              CSR_UEPC,
              CSR_UTVEC,
              CSR_UCAUSE :
                if (!PULP_SECURE) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            default : csr_illegal = 1'b1;

          endcase // case (instr_rdata_i[31:20])

          illegal_insn_o = csr_illegal;

        end

      end


      ///////////////////////////////////////////////
      //  _   ___        ___     ___   ___  ____   //
      // | | | \ \      / / |   / _ \ / _ \|  _ \  //
      // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
      // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
      // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
      //                                           //
      ///////////////////////////////////////////////

      OPCODE_HWLOOP: begin
        if(PULP_XPULP) begin : HWLOOP_FEATURE_ENABLED
          hwlp_target_mux_sel_o = 1'b0;

          unique case (instr_rdata_i[14:12])
            3'b000: begin
              // lp.starti: set start address to PC + I-type immediate
              hwlp_we[0]           = 1'b1;
              hwlp_start_mux_sel_o = 1'b0;
            end

            3'b001: begin
              // lp.endi: set end address to PC + I-type immediate
              hwlp_we[1]         = 1'b1;
            end

            3'b010: begin
              // lp.count: initialize counter from rs1
              hwlp_we[2]         = 1'b1;
              hwlp_cnt_mux_sel_o = 1'b1;
              rega_used_o        = 1'b1;
            end

            3'b011: begin
              // lp.counti: initialize counter from I-type immediate
              hwlp_we[2]         = 1'b1;
              hwlp_cnt_mux_sel_o = 1'b0;
            end

            3'b100: begin
              // lp.setup: initialize counter from rs1, set start address to
              // next instruction and end address to PC + I-type immediate
              hwlp_we              = 3'b111;
              hwlp_start_mux_sel_o = 1'b1;
              hwlp_cnt_mux_sel_o   = 1'b1;
              rega_used_o          = 1'b1;
            end

            3'b101: begin
              // lp.setupi: initialize counter from immediate, set start address to
              // next instruction and end address to PC + I-type immediate
              hwlp_we               = 3'b111;
              hwlp_target_mux_sel_o = 1'b1;
              hwlp_start_mux_sel_o  = 1'b1;
              hwlp_cnt_mux_sel_o    = 1'b0;
            end

            default: begin
              illegal_insn_o = 1'b1;
            end
          endcase // case (instr_rdata_i[14:12])

        end else begin // block: HWLOOP_FEATURE_ENABLED
          illegal_insn_o = 1'b1;
        end
      end // case: OPCODE_HWLOOP

      default: begin
        illegal_insn_o = 1'b1;
      end
    endcase


    // make sure invalid compressed instruction causes an exception
    if (illegal_c_insn_i) begin
      illegal_insn_o = 1'b1;
    end

  end

  // deassert we signals (in case of stalls)
  assign alu_en_o                    = (deassert_we_i) ? 1'b0          : alu_en;
  assign apu_en_o                    = (deassert_we_i) ? 1'b0          : apu_en;
  assign mult_int_en_o               = (deassert_we_i) ? 1'b0          : mult_int_en;
  assign mult_dot_en_o               = (deassert_we_i) ? 1'b0          : mult_dot_en;
  assign regfile_mem_we_o            = (deassert_we_i) ? 1'b0          : regfile_mem_we;
  assign regfile_alu_we_o            = (deassert_we_i) ? 1'b0          : regfile_alu_we;
  assign data_req_o                  = (deassert_we_i) ? 1'b0          : data_req;
  assign hwlp_we_o                   = (deassert_we_i) ? 3'b0          : hwlp_we;
  assign csr_op_o                    = (deassert_we_i) ? CSR_OP_READ   : csr_op;
  assign ctrl_transfer_insn_in_id_o  = (deassert_we_i) ? BRANCH_NONE   : ctrl_transfer_insn;

  assign ctrl_transfer_insn_in_dec_o  = ctrl_transfer_insn;
  assign regfile_alu_we_dec_o         = regfile_alu_we;

endmodule // cv32e40x_decoder
