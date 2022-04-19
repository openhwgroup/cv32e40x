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
//                 Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Design Name:    I Decoder                                                  //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the RV32I Base Instruction set + C             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_i_decoder import cv32e40x_pkg::*;
  #(
    parameter DEBUG_TRIGGER_EN  = 1
    )
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,

   input  ctrl_fsm_t     ctrl_fsm_i, // todo:low each use of this signal needs a comment explaining why the signal from the controller is safe to be used with ID timing (probably add comment in FSM)
   output decoder_ctrl_t decoder_ctrl_o
   );

  always_comb
  begin

    // Default assignments
    decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
    decoder_ctrl_o.illegal_insn = 1'b0;

    unique case (instr_rdata_i[1:0])

      //////////////////////////////////////////////////////////////////////////////////////////////////////
      //   ____                                                 _   ____                     _            //
      //  / ___|___  _ __ ___  _ __  _ __ ___  ___ ___  ___  __| | |  _ \  ___  ___ ___   __| | ___ _ __  //
      // | |   / _ \| '_ ` _ \| '_ \| '__/ _ \/ __/ __|/ _ \/ _` | | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
      // | |__| (_) | | | | | | |_) | | |  __/\__ \__ \  __/ (_| | | |_| |  __/ (_| (_) | (_| |  __/ |    //
      //  \____\___/|_| |_| |_| .__/|_|  \___||___/___/\___|\__,_| |____/ \___|\___\___/ \__,_|\___|_|    //
      //                      |_|                                                                         //
      //////////////////////////////////////////////////////////////////////////////////////////////////////

      // C0
      2'b00: begin
        unique case (instr_rdata_i[15:13])
          3'b000: begin
            // c.addi4spn -> addi rd', x2, imm
            decoder_ctrl_o.alu_en           = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_CIW;
            decoder_ctrl_o.rf_we            = 1'b1;
            decoder_ctrl_o.rf_re[0]         = 1'b1;
            decoder_ctrl_o.alu_operator     = ALU_ADD; // Add Immediate
            if (instr_rdata_i[12:5] == 8'b0) begin
              decoder_ctrl_o.illegal_insn = 1'b1;
            end
          end

          3'b010: begin
            // c.lw -> lw rd', imm(rs1')
            decoder_ctrl_o.lsu_en           = 1'b1;
            decoder_ctrl_o.rf_we            = 1'b1;
            decoder_ctrl_o.rf_re[0]         = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
            decoder_ctrl_o.op_c_mux_sel     = OP_C_NONE;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_CL;
            decoder_ctrl_o.lsu_sext         = 1'b0;
            decoder_ctrl_o.lsu_size         = 2'b10;
          end

          3'b110: begin
            // c.sw -> sw rs2', imm(rs1')
            // todo instr_o.bus_resp.rdata = {5'b0, instr[5], instr[12], 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b010, instr[11:10], instr[6], 2'b00, OPCODE_STORE};
          end

          3'b001,       // c.fld -> fld rd', imm(rs1')
          3'b011,       // c.flw -> flw rd', imm(rs1')
          3'b101,       // c.fsd -> fsd rs2', imm(rs1')
          3'b111: begin // c.fsw -> fsw rs2', imm(rs1')
            decoder_ctrl_o.illegal_insn = 1'b1;
            // todo instr_o.bus_resp.rdata = {5'b0, instr[5], instr[12:10], instr[6], 2'b00, 2'b01, instr[9:7], 3'b010, 2'b01, instr[4:2], OPCODE_LOAD};
          end
          default: begin
            // todo instr_o.bus_resp.rdata = {5'b0, instr[5], instr[12:10], instr[6], 2'b00, 2'b01, instr[9:7], 3'b010, 2'b01, instr[4:2], OPCODE_LOAD};
            decoder_ctrl_o.illegal_insn = 1'b1;
          end
        endcase
      end

      // C1
      2'b01: begin
        unique case (instr_rdata_i[15:13])
          3'b000: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop
            // todo instr_o.bus_resp.rdata = {{6 {instr[12]}}, instr[12], instr[6:2], instr[11:7], 3'b0, instr[11:7], OPCODE_OPIMM};
          end

          3'b001, 3'b101: begin
            // 001: c.jal -> jal x1, imm
            // 101: c.j   -> jal x0, imm
            // todo instr_o.bus_resp.rdata = {instr[12], instr[8], instr[10:9], instr[6], instr[7], instr[2], instr[11], instr[5:3], {9 {instr[12]}}, 4'b0, ~instr[15], OPCODE_JAL};
          end

          3'b010: begin
            if (instr_rdata_i[11:7] == 5'b0) begin
              // Hint -> addi x0, x0, nzimm
              // todo instr_o.bus_resp.rdata = {{6 {instr[12]}}, instr[12], instr[6:2], 5'b0, 3'b0, instr[11:7], OPCODE_OPIMM};
            end else begin
              // c.li -> addi rd, x0, nzimm
              // todo instr_o.bus_resp.rdata = {{6 {instr[12]}}, instr[12], instr[6:2], 5'b0, 3'b0, instr[11:7], OPCODE_OPIMM};
            end
          end

          3'b011: begin
            if ({instr_rdata_i[12], instr_rdata_i[6:2]} == 6'b0) begin
              // todo instr_o.bus_resp.rdata = {{15 {instr[12]}}, instr[6:2], instr[11:7], OPCODE_LUI};
              decoder_ctrl_o.illegal_insn = 1'b1;
            end else begin
              if (instr_rdata_i[11:7] == 5'h02) begin
                // c.addi16sp -> addi x2, x2, nzimm
                // todo instr_o.bus_resp.rdata = {{3 {instr[12]}}, instr[4:3], instr[5], instr[2], instr[6], 4'b0, 5'h02, 3'b000, 5'h02, OPCODE_OPIMM};
              end else if (instr_rdata_i[11:7] == 5'b0) begin
                // Hint -> lui x0, imm
                // todo instr_o.bus_resp.rdata = {{15 {instr[12]}}, instr[6:2], instr[11:7], OPCODE_LUI};
              end else begin
                // c.lui -> lui rd, imm
                // todo instr_o.bus_resp.rdata = {{15 {instr[12]}}, instr[6:2], instr[11:7], OPCODE_LUI};
              end
            end
          end

          3'b100: begin
            unique case (instr_rdata_i[11:10])
              2'b00,
              2'b01: begin
                // 00: c.srli -> srli rd, rd, shamt
                // 01: c.srai -> srai rd, rd, shamt
                if (instr_rdata_i[12] == 1'b1) begin
                  // Reserved for future custom extensions (instr_o don't care)
                  // todo instr_o.bus_resp.rdata = {1'b0, instr[10], 5'b0, instr[6:2], 2'b01, instr[9:7], 3'b101, 2'b01, instr[9:7], OPCODE_OPIMM};
                  decoder_ctrl_o.illegal_insn = 1'b1;
                end else begin
                  if (instr_rdata_i[6:2] == 5'b0) begin
                    // Hint
                    // todo instr_o.bus_resp.rdata = {1'b0, instr[10], 5'b0, instr[6:2], 2'b01, instr[9:7], 3'b101, 2'b01, instr[9:7], OPCODE_OPIMM};
                  end else begin
                    // todo instr_o.bus_resp.rdata = {1'b0, instr[10], 5'b0, instr[6:2], 2'b01, instr[9:7], 3'b101, 2'b01, instr[9:7], OPCODE_OPIMM};
                  end
                end
              end

              2'b10: begin
                // c.andi -> andi rd, rd, imm
                // todo instr_o.bus_resp.rdata = {{6 {instr[12]}}, instr[12], instr[6:2], 2'b01, instr[9:7], 3'b111, 2'b01, instr[9:7], OPCODE_OPIMM};
              end

              2'b11: begin
                unique case ({instr_rdata_i[12], instr_rdata_i[6:5]})
                  3'b000: begin
                    // c.sub -> sub rd', rd', rs2'
                    // todo instr_o.bus_resp.rdata = {2'b01, 5'b0, 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b000, 2'b01, instr[9:7], OPCODE_OP};
                  end

                  3'b001: begin
                    // c.xor -> xor rd', rd', rs2'
                    // todo instr_o.bus_resp.rdata = {7'b0, 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b100, 2'b01, instr[9:7], OPCODE_OP};
                  end

                  3'b010: begin
                    // c.or  -> or  rd', rd', rs2'
                    // todo instr_o.bus_resp.rdata = {7'b0, 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b110, 2'b01, instr[9:7], OPCODE_OP};
                  end

                  3'b011: begin
                    // c.and -> and rd', rd', rs2'
                    // todo instr_o.bus_resp.rdata = {7'b0, 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b111, 2'b01, instr[9:7], OPCODE_OP};
                  end

                  3'b100,
                  3'b101,
                  3'b110,
                  3'b111: begin
                    // 100: c.subw
                    // 101: c.addw
                    // todo instr_o.bus_resp.rdata = {7'b0, 2'b01, instr[4:2], 2'b01, instr[9:7], 3'b111, 2'b01, instr[9:7], OPCODE_OP};
                    decoder_ctrl_o.illegal_insn = 1'b1;
                  end
                endcase
              end
            endcase
          end

          3'b110, 3'b111: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            // todo instr_o.bus_resp.rdata = {{4 {instr[12]}}, instr[6:5], instr[2], 5'b0, 2'b01, instr[9:7], 2'b00, instr[13], instr[11:10], instr[4:3], instr[12], OPCODE_BRANCH};
          end
        endcase
      end

      // C2
      2'b10: begin
        unique case (instr_rdata_i[15:13])
          3'b000: begin
            if (instr_rdata_i[12] == 1'b1) begin
              // Reserved for future extensions (instr_o don't care)
              // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], instr[11:7], 3'b001, instr[11:7], OPCODE_OPIMM};
              decoder_ctrl_o.illegal_insn = 1'b1;
            end else begin
              if ((instr_rdata_i[6:2] == 5'b0) || (instr_rdata_i[11:7] == 5'b0)) begin
                // Hint -> slli rd, rd, shamt
                // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], instr[11:7], 3'b001, instr[11:7], OPCODE_OPIMM};
              end else begin
                // c.slli -> slli rd, rd, shamt
                // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], instr[11:7], 3'b001, instr[11:7], OPCODE_OPIMM};
              end
            end
          end

          3'b010: begin
            // c.lwsp -> lw rd, imm(x2)
            // todo instr_o.bus_resp.rdata = {4'b0, instr[3:2], instr[12], instr[6:4], 2'b00, 5'h02, 3'b010, instr[11:7], OPCODE_LOAD};
            if (instr_rdata_i[11:7] == 5'b0) begin
              decoder_ctrl_o.illegal_insn = 1'b1;
            end
          end

          3'b100: begin
            if (instr_rdata_i[12] == 1'b0) begin
              if (instr_rdata_i[6:2] == 5'b0) begin
                // c.jr -> jalr x0, rd/rs1, 0
                // todo instr_o.bus_resp.rdata = {12'b0, instr[11:7], 3'b0, 5'b0, OPCODE_JALR};
                // c.jr with rs1 = 0 is reserved
                if (instr_rdata_i[11:7] == 5'b0) begin
                  decoder_ctrl_o.illegal_insn = 1'b1;
                end
              end else begin
                if (instr_rdata_i[11:7] == 5'b0) begin
                  // Hint -> add x0, x0, rs2
                  // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], 5'b0, 3'b0, instr[11:7], OPCODE_OP};
                end else begin
                  // c.mv -> add rd, x0, rs2
                  // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], 5'b0, 3'b0, instr[11:7], OPCODE_OP};
                end
              end
            end else begin
              if (instr_rdata_i[6:2] == 5'b0) begin
                if (instr_rdata_i[11:7] == 5'b0) begin
                  // c.ebreak -> ebreak
                  // todo instr_o.bus_resp.rdata = {32'h00_10_00_73};
                end else begin
                  // c.jalr -> jalr x1, rs1, 0
                  // todo instr_o.bus_resp.rdata = {12'b0, instr[11:7], 3'b000, 5'b00001, OPCODE_JALR};
                end
              end else begin
                if (instr_rdata_i[11:7] == 5'b0) begin
                  // Hint -> add x0, x0, rs2
                  // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], instr[11:7], 3'b0, instr[11:7], OPCODE_OP};
                end else begin
                  // c.add -> add rd, rd, rs2
                  // todo instr_o.bus_resp.rdata = {7'b0, instr[6:2], instr[11:7], 3'b0, instr[11:7], OPCODE_OP};
                end
              end
            end
          end

          3'b110: begin
            // c.swsp -> sw rs2, imm(x2)
            // todo instr_o.bus_resp.rdata = {4'b0, instr[8:7], instr[12], instr[6:2], 5'h02, 3'b010, instr[11:9], 2'b00, OPCODE_STORE};
          end

          3'b001,        // c.fldsp -> fld rd, imm(x2)
          3'b011,        // c.flwsp -> flw rd, imm(x2)
          3'b101,        // c.fsdsp -> fsd rs2, imm(x2)
          3'b111: begin  // c.fswsp -> fsw rs2, imm(x2)
            // todo instr_o.bus_resp.rdata = {4'b0, instr[3:2], instr[12], instr[6:4], 2'b00, 5'h02, 3'b010, instr[11:7], OPCODE_LOAD};
            decoder_ctrl_o.illegal_insn = 1'b1;
          end
        endcase
      end

      ////////////////////////////////////////////////
      //  _   ____                     _            //
      // | | |  _ \  ___  ___ ___   __| | ___ _ __  //
      // | | | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
      // | | | |_| |  __/ (_| (_) | (_| |  __/ |    //
      // |_| |____/ \___|\___\___/ \__,_|\___|_|    //
      //                                            //
      ////////////////////////////////////////////////

      default: begin
        // 32 bit (or more) instruction

        unique case (instr_rdata_i[6:0])

          //////////////////////////////////////
          //      _ _   _ __  __ ____  ____   //
          //     | | | | |  \/  |  _ \/ ___|  //
          //  _  | | | | | |\/| | |_) \___ \  //
          // | |_| | |_| | |  | |  __/ ___) | //
          //  \___/ \___/|_|  |_|_|   |____/  //
          //                                  //
          //////////////////////////////////////

          OPCODE_JAL: begin // Jump and Link
            decoder_ctrl_o.alu_en                       = 1'b1;             // ALU computes link address (PC+2/4)
            decoder_ctrl_o.alu_jmp                      = 1'b1;
            decoder_ctrl_o.alu_jmpr                     = 1'b0;             // No register used (rf_re[0] = 0) (used for hazard detection)
            decoder_ctrl_o.alu_op_a_mux_sel             = OP_A_CURRPC;
            decoder_ctrl_o.alu_op_b_mux_sel             = OP_B_IMM;         // PC increment (2 or 4) for link address
            decoder_ctrl_o.imm_b_mux_sel                = IMMB_PCINCR;
            decoder_ctrl_o.alu_operator                 = ALU_ADD;
            decoder_ctrl_o.rf_we                        = 1'b1;             // Write LR
            decoder_ctrl_o.rf_re[0]                     = 1'b0;             // Calculate jump target (= PC + UJ imm)
            decoder_ctrl_o.rf_re[1]                     = 1'b0;             // Calculate jump target (= PC + UJ imm)
            decoder_ctrl_o.bch_jmp_mux_sel              = CT_JAL;
          end

          OPCODE_JALR: begin // Jump and Link Register
            if (instr_rdata_i[14:12] != 3'b0) begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end else begin
              decoder_ctrl_o.alu_en                     = 1'b1;             // ALU computes link address (PC+2/4)
              decoder_ctrl_o.alu_jmp                    = 1'b1;
              decoder_ctrl_o.alu_jmpr                   = 1'b1;             // Register used (rf_re[0] = 1) (used for hazard detection)
              decoder_ctrl_o.alu_op_a_mux_sel           = OP_A_CURRPC;
              decoder_ctrl_o.alu_op_b_mux_sel           = OP_B_IMM;         // PC increment (2 or 4) for link address
              decoder_ctrl_o.imm_b_mux_sel              = IMMB_PCINCR;
              decoder_ctrl_o.alu_operator               = ALU_ADD;
              decoder_ctrl_o.rf_we                      = 1'b1;             // Write LR
              decoder_ctrl_o.rf_re[0]                   = 1'b1;             // Calculate jump target (= RS1 + I imm)
              decoder_ctrl_o.rf_re[1]                   = 1'b0;             // Calculate jump target (= RS1 + I imm)
              decoder_ctrl_o.bch_jmp_mux_sel            = CT_JALR;
            end
          end

          OPCODE_BRANCH: begin // Branch
            decoder_ctrl_o.alu_en                       = 1'b1;
            decoder_ctrl_o.alu_bch                      = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel             = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel             = OP_B_REGB_OR_FWD;
            decoder_ctrl_o.op_c_mux_sel                 = OP_C_BCH;
            decoder_ctrl_o.rf_we                        = 1'b0;             // No result write
            decoder_ctrl_o.rf_re[0]                     = 1'b1;
            decoder_ctrl_o.rf_re[1]                     = 1'b1;
            decoder_ctrl_o.bch_jmp_mux_sel              = CT_BCH;

            unique case (instr_rdata_i[14:12])
              3'b000: decoder_ctrl_o.alu_operator = ALU_EQ;
              3'b001: decoder_ctrl_o.alu_operator = ALU_NE;
              3'b100: decoder_ctrl_o.alu_operator = ALU_LT;
              3'b101: decoder_ctrl_o.alu_operator = ALU_GE;
              3'b110: decoder_ctrl_o.alu_operator = ALU_LTU;
              3'b111: decoder_ctrl_o.alu_operator = ALU_GEU;
              default: begin
                decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
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

          OPCODE_STORE: begin
            decoder_ctrl_o.lsu_en           = 1'b1;
            decoder_ctrl_o.lsu_we           = 1'b1;
            decoder_ctrl_o.rf_re[0]         = 1'b1;
            decoder_ctrl_o.rf_re[1]         = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;             // Offset from immediate
            decoder_ctrl_o.op_c_mux_sel     = OP_C_REGB_OR_FWD;     // Used for write data
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_S;

            // Data size encoded in instr_rdata_i[13:12]:
            // 2'b00: SB, 2'b01: SH, 2'10: SW
            decoder_ctrl_o.lsu_size = instr_rdata_i[13:12];

            if ((instr_rdata_i[14] == 1'b1) || (instr_rdata_i[13:12] == 2'b11)) begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end
          end

          OPCODE_LOAD: begin
            decoder_ctrl_o.lsu_en           = 1'b1;
            decoder_ctrl_o.rf_we            = 1'b1;
            decoder_ctrl_o.rf_re[0]         = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;             // Offset from immediate
            decoder_ctrl_o.op_c_mux_sel     = OP_C_NONE;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_I;

            // Sign/zero extension
            decoder_ctrl_o.lsu_sext = !instr_rdata_i[14];

            // Data size encoded in instr_rdata_i[13:12]:
            // 2'b00: LB, 2'b01: LH, 2'10: LW
            decoder_ctrl_o.lsu_size = instr_rdata_i[13:12];

            // Reserved or RV64
            if ((instr_rdata_i[14:12] == 3'b111) || (instr_rdata_i[14:12] == 3'b110) || (instr_rdata_i[14:12] == 3'b011)) begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
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

          OPCODE_LUI: begin // Load Upper Immediate
            decoder_ctrl_o.alu_en           = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_IMM;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
            decoder_ctrl_o.imm_a_mux_sel    = IMMA_ZERO;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_U;
            decoder_ctrl_o.alu_operator     = ALU_ADD;
            decoder_ctrl_o.rf_we            = 1'b1;
          end

          OPCODE_AUIPC: begin // Add Upper Immediate to PC
            decoder_ctrl_o.alu_en           = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_CURRPC;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_U;
            decoder_ctrl_o.alu_operator     = ALU_ADD;
            decoder_ctrl_o.rf_we            = 1'b1;
          end

          OPCODE_OPIMM: begin // Register-Immediate ALU Operations
            decoder_ctrl_o.alu_en           = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
            decoder_ctrl_o.imm_b_mux_sel    = IMMB_I;
            decoder_ctrl_o.rf_we            = 1'b1;
            decoder_ctrl_o.rf_re[0]         = 1'b1;

            unique case (instr_rdata_i[14:12])
              3'b000: decoder_ctrl_o.alu_operator = ALU_ADD;  // Add Immediate
              3'b010: decoder_ctrl_o.alu_operator = ALU_SLT;  // Set to one if Lower Than Immediate
              3'b011: decoder_ctrl_o.alu_operator = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
              3'b100: decoder_ctrl_o.alu_operator = ALU_XOR;  // Exclusive Or with Immediate
              3'b110: decoder_ctrl_o.alu_operator = ALU_OR;   // Or with Immediate
              3'b111: decoder_ctrl_o.alu_operator = ALU_AND;  // And with Immediate

              3'b001: begin
                decoder_ctrl_o.alu_operator = ALU_SLL;        // Shift Left Logical by Immediate
                if (instr_rdata_i[31:25] != 7'b0) begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end
              end

              3'b101: begin
                if (instr_rdata_i[31:25] == 7'b0) begin
                  decoder_ctrl_o.alu_operator = ALU_SRL;      // Shift Right Logical by Immediate
                end else if (instr_rdata_i[31:25] == 7'b010_0000) begin
                  decoder_ctrl_o.alu_operator = ALU_SRA;      // Shift Right Arithmetically by Immediate
                end else begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end
              end
            endcase
          end

          OPCODE_OP: begin  // Register-Register ALU operation
            if ((instr_rdata_i[31:30] == 2'b11) || (instr_rdata_i[31:30] == 2'b10)) begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end else begin
              decoder_ctrl_o.alu_en           = 1'b1;
              decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
              decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGB_OR_FWD;
              decoder_ctrl_o.rf_we            = 1'b1;
              decoder_ctrl_o.rf_re[0]         = 1'b1;

              if (!instr_rdata_i[28]) begin
                decoder_ctrl_o.rf_re[1] = 1'b1;
              end

              unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
                // RV32I ALU operations
                {6'b00_0000, 3'b000}: decoder_ctrl_o.alu_operator = ALU_ADD;  // Add
                {6'b10_0000, 3'b000}: decoder_ctrl_o.alu_operator = ALU_SUB;  // Sub
                {6'b00_0000, 3'b010}: decoder_ctrl_o.alu_operator = ALU_SLT;  // Set Lower Than
                {6'b00_0000, 3'b011}: decoder_ctrl_o.alu_operator = ALU_SLTU; // Set Lower Than Unsigned
                {6'b00_0000, 3'b100}: decoder_ctrl_o.alu_operator = ALU_XOR;  // Xor
                {6'b00_0000, 3'b110}: decoder_ctrl_o.alu_operator = ALU_OR;   // Or
                {6'b00_0000, 3'b111}: decoder_ctrl_o.alu_operator = ALU_AND;  // And
                {6'b00_0000, 3'b001}: decoder_ctrl_o.alu_operator = ALU_SLL;  // Shift Left Logical
                {6'b00_0000, 3'b101}: decoder_ctrl_o.alu_operator = ALU_SRL;  // Shift Right Logical
                {6'b10_0000, 3'b101}: decoder_ctrl_o.alu_operator = ALU_SRA;  // Shift Right Arithmetic
                default: begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end
              endcase
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
            decoder_ctrl_o.sys_en = 1'b1;
            // todo: We may not want the fence handshake for regular (none .i) fences
            unique case (instr_rdata_i[14:12])
              3'b000: begin // FENCE (FENCE.I instead, a bit more conservative)
                // Flush pipeline
                decoder_ctrl_o.sys_fencei_insn = 1'b1;
              end

              3'b001: begin // FENCE.I
                // Flush prefetch buffer, flush pipeline
                decoder_ctrl_o.sys_fencei_insn = 1'b1;
              end

              default: begin
                decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
              end
            endcase
          end

          OPCODE_SYSTEM: begin
            if (instr_rdata_i[14:12] == 3'b000) begin // Non CSR related SYSTEM instructions
              if ({instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0) begin
                decoder_ctrl_o.sys_en = 1'b1;

                unique case (instr_rdata_i[31:20])
                  12'h000: begin // ecall
                    // Environment (system) call
                    decoder_ctrl_o.sys_ecall_insn  = 1'b1;
                  end

                  12'h001: begin // ebreak
                    // Debugger trap
                    decoder_ctrl_o.sys_ebrk_insn = 1'b1;
                  end

                  12'h302: begin // mret
                    decoder_ctrl_o.sys_mret_insn = 1'b1;
                  end

                  12'h7b2: begin // dret
                    if (ctrl_fsm_i.debug_mode) begin
                      decoder_ctrl_o.sys_dret_insn    =  1'b1;
                    end else begin
                      decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                    end
                  end

                  12'h105: begin // wfi
                    // Suppressing WFI in case of ctrl_fsm_i.debug_wfi_no_sleep to prevent sleeping when not allowed.
                    decoder_ctrl_o.sys_wfi_insn = ctrl_fsm_i.debug_wfi_no_sleep ? 1'b0 : 1'b1;
                  end

                  default: begin
                    decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                  end
                endcase
              end else begin // if ({instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0)
                decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
              end
            end else begin // CSR instructions
              decoder_ctrl_o.csr_en = 1'b1;
              decoder_ctrl_o.rf_we  = 1'b1;

              if (instr_rdata_i[14] == 1'b1) begin
                // rs1 field is used as immediate
                decoder_ctrl_o.alu_op_a_mux_sel = OP_A_IMM;
              end else begin
                decoder_ctrl_o.rf_re[0]         = 1'b1;
                decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
              end

              decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
              decoder_ctrl_o.imm_a_mux_sel    = IMMA_Z;
              decoder_ctrl_o.imm_b_mux_sel    = IMMB_I; // CSR address is encoded in I imm

              // instr_rdata_i[19:14] = rs or immediate value
              // If set or clear with rs==x0 or imm==0, then do not perform a write action
              unique case (instr_rdata_i[13:12])
                2'b01:   decoder_ctrl_o.csr_op = CSR_OP_WRITE;
                2'b10:   decoder_ctrl_o.csr_op = (instr_rdata_i[19:15] == 5'b0) ? CSR_OP_READ : CSR_OP_SET;
                2'b11:   decoder_ctrl_o.csr_op = (instr_rdata_i[19:15] == 5'b0) ? CSR_OP_READ : CSR_OP_CLEAR;
                default: decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
              endcase
            end
          end

          default: begin
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        endcase

      end
    endcase

  end // always_comb

endmodule : cv32e40x_i_decoder
