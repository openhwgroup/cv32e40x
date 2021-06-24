// Copyright 2021 Silicon Labs, Inc.
//   
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//   
//     https://solderpad.org/licenses/SHL-2.0/
//   
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Design Name:    B Decoder                                                  //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the RV32B extension                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_b_decoder import cv32e40x_pkg::*;
  #(parameter b_ext_e B_EXT = NONE)
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,
   output             decoder_ctrl_t decoder_ctrl_o
   );

  localparam RV32B_ZBA = (B_EXT == ZBA_ZBB_ZBS) || (B_EXT == ZBA_ZBB_ZBC_ZBS);
  localparam RV32B_ZBB = (B_EXT == ZBA_ZBB_ZBS) || (B_EXT == ZBA_ZBB_ZBC_ZBS);
  localparam RV32B_ZBS = (B_EXT == ZBA_ZBB_ZBS) || (B_EXT == ZBA_ZBB_ZBC_ZBS);
  localparam RV32B_ZBC = (B_EXT == ZBA_ZBB_ZBC_ZBS);
  
  always_comb
  begin

    // Default assignment
    decoder_ctrl_o                  = DECODER_CTRL_ILLEGAL_INSN;

    // Common signals for all instructions
    decoder_ctrl_o.rf_re[0]         = 1'b1;
    decoder_ctrl_o.rf_re[1]         = 1'b1;
    decoder_ctrl_o.rf_we            = 1'b1;
    decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
    decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGB_OR_FWD;
    decoder_ctrl_o.alu_en           = 1'b1;

    unique case (instr_rdata_i[6:0])

      OPCODE_OP: begin

        unique case ({instr_rdata_i[31:25], instr_rdata_i[14:12]})

          // Supported RV32B Zca instructions
          {7'b001_0000, 3'b010}: begin // Shift left by 1 and add (sh1add)
            if (RV32B_ZBA) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_SH1ADD;
            end
          end
          {7'b001_0000, 3'b100}: begin // Shift left by 2 and add (sh2add)
            if (RV32B_ZBA) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_SH2ADD;
            end
          end
          {7'b001_0000, 3'b110}: begin // Shift left by 3 and add (sh3add)
            if (RV32B_ZBA) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_SH3ADD;
            end
          end

          default: begin
            // No match
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        endcase

      end // case: OPCODE_OP


      OPCODE_OPIMM: begin

        unique case ({instr_rdata_i[31:25], instr_rdata_i[24:20], instr_rdata_i[14:12]})
          {7'b011_0000, 5'b0_0000, 3'b001} : begin
            if (RV32B_ZBB) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_CLZ;
            end
          end
          {7'b011_0000, 5'b0_0001, 3'b001} : begin
            if (RV32B_ZBB) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_CTZ;
            end
          end
          {7'b011_0000, 5'b0_0010, 3'b001} : begin
            if (RV32B_ZBB) begin
              decoder_ctrl_o.illegal_insn = 1'b0;
              decoder_ctrl_o.alu_operator = ALU_B_CPOP;
            end
          end
          default: begin
            // No match
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        endcase
      end // case: OPCODE_OPIMM

      default: begin
        // No match
        decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
      end

    endcase // unique case (instr_rdata_i[6:0])
    
  end // always_comb

endmodule : cv32e40x_b_decoder
