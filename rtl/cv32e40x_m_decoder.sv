// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer        Oivind Ekelund- oivind.ekelund@silabs.com                  //
//                                                                            //
// Design Name:    M Decoder                                                  //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the RV32M extension                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_m_decoder import cv32e40x_pkg::*;
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,

   output             decoder_ctrl_t decoder_ctrl_o
   );
  
  always_comb
  begin

    // Default assignment (including decoder_ctrl_o.match = 0)
    decoder_ctrl_o = DECODER_CTRL_IDLE;

    // Common signals for all MUL/DIV (will be ignored if decoder_ctrl_o.match = 0)
    decoder_ctrl_o.rf_we    = 1'b1;
    decoder_ctrl_o.rf_re[0] = 1'b1;
    decoder_ctrl_o.rf_re[1] = 1'b1;

    unique case (instr_rdata_i[6:0])
     
      OPCODE_OP: begin

        unique case ({instr_rdata_i[31:25], instr_rdata_i[14:12]})

          // supported RV32M instructions
          {7'b000_0001, 3'b000}: begin // mul
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_en           = 1'b0;
            decoder_ctrl_o.mult_en          = 1'b1;
            decoder_ctrl_o.mult_operator    = MUL_M32;
          end
          {7'b000_0001, 3'b001}: begin // mulh
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_en           = 1'b0;
            decoder_ctrl_o.mult_signed_mode = 2'b11;
            decoder_ctrl_o.mult_en          = 1'b1;
            decoder_ctrl_o.mult_operator    = MUL_H;
          end
          {7'b000_0001, 3'b010}: begin // mulhsu
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_en           = 1'b0;
            decoder_ctrl_o.mult_signed_mode = 2'b01;
            decoder_ctrl_o.mult_en          = 1'b1;
            decoder_ctrl_o.mult_operator    = MUL_H;
          end
          {7'b000_0001, 3'b011}: begin // mulhu
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_en           = 1'b0;
            decoder_ctrl_o.mult_signed_mode = 2'b00;
            decoder_ctrl_o.mult_en          = 1'b1;
            decoder_ctrl_o.mult_operator    = MUL_H;
          end
          {7'b000_0001, 3'b100}: begin // div
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGB_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGA_OR_FWD;
            decoder_ctrl_o.alu_operator     = ALU_DIV;
          end
          {7'b000_0001, 3'b101}: begin // divu
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGB_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGA_OR_FWD;
            decoder_ctrl_o.alu_operator     = ALU_DIVU;
          end
          {7'b000_0001, 3'b110}: begin // rem
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGB_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGA_OR_FWD;
            decoder_ctrl_o.alu_operator     = ALU_REM;
          end
          {7'b000_0001, 3'b111}: begin // remu
            decoder_ctrl_o.match            = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGB_OR_FWD;
            decoder_ctrl_o.alu_op_b_mux_sel = OP_B_REGA_OR_FWD;
            decoder_ctrl_o.alu_operator     = ALU_REMU;
          end

          default: begin
            // No match, keep decoder_ctrl_o.match = 1'b0
          end
        endcase

      end // case: OPCODE_OP
      
      default: begin
        // No match, keep decoder_ctrl_o.match = 1'b0
      end
      
    endcase // unique case (instr_rdata_i[6:0])
    
  end // always_comb

endmodule : cv32e40x_m_decoder
