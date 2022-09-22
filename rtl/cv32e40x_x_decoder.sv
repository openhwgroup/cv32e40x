// Copyright 2022 Silicon Labs, Inc.
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
//                                                                            //
// Authors:        Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    Decoder for custom instructions                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_x_decoder import cv32e40x_pkg::*;
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,
   input  ctrl_fsm_t     ctrl_fsm_i,
   output             decoder_ctrl_t decoder_ctrl_o
   );

  always_comb
  begin

    // Default assignments
    decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
    decoder_ctrl_o.illegal_insn = 1'b0;

    unique case (instr_rdata_i[6:0])

      OPCODE_SYSTEM: begin
        if (instr_rdata_i[14:12] == 3'b000) begin
          if ({instr_rdata_i[25:15], instr_rdata_i[11:7]} == '0) begin
            if (instr_rdata_i[31:26] == 6'b100011) begin
              // WFE instructions
              decoder_ctrl_o.sys_en = 1'b1;

              // Suppressing WFI in case of ctrl_fsm_i.debug_wfi_no_sleep to prevent sleeping when not allowed.
              decoder_ctrl_o.sys_wfe_insn = ctrl_fsm_i.debug_wfi_no_sleep ? 1'b0 : 1'b1;
            end else begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end
          end else begin
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        end else begin
          decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
        end
      end
      default: begin
        // No match
        decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
      end
    endcase

  end

endmodule

