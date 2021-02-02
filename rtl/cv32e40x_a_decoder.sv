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
// Engineer        Oivind Ekelund- oivind.ekelund@silabs.com                  //
//                                                                            //
// Design Name:    A Decoder                                                  //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the A extension                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_a_decoder import cv32e40x_pkg::*;
  #(
    parameter A_EXTENSION       = 0
    )
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,
  
   output             decoder_ctrl_t decoder_ctrl_o
   );
  
  always_comb
  begin
    
    decoder_ctrl_o = DECODER_CTRL_IDLE;

    unique case (instr_rdata_i[6:0])

      OPCODE_AMO: begin
        if (A_EXTENSION) begin : decode_amo
          if (instr_rdata_i[14:12] == 3'b010) begin // RV32A Extension (word)

            decoder_ctrl_o.match             = 1'b1;
            
            decoder_ctrl_o.data_req          = 1'b1;
            decoder_ctrl_o.data_type_o       = 2'b00;
            decoder_ctrl_o.rf_re_o[0]        = 1'b1;
            decoder_ctrl_o.rf_re_o[1]        = 1'b1;
            decoder_ctrl_o.rf_we             = 1'b1;
            decoder_ctrl_o.prepost_useincr_o = 1'b0; // only use alu_operand_a as address (not a+b)
            decoder_ctrl_o.alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;

            decoder_ctrl_o.data_sign_extension_o = 1'b1;

            // Apply AMO instruction at `data_atop_o`.
            decoder_ctrl_o.data_atop_o = {1'b1, instr_rdata_i[31:27]};

            unique case (instr_rdata_i[31:27])
              AMO_LR: begin
                //decoder_ctrl_o.match     = 1'b1;
                decoder_ctrl_o.data_we_o = 1'b0;
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
                decoder_ctrl_o.data_we_o = 1'b1;
                decoder_ctrl_o.alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD; // pass write data through ALU operand c
              end
              default : decoder_ctrl_o.illegal_insn_o = 1'b1;
            endcase
          end
          else begin
            decoder_ctrl_o.illegal_insn_o = 1'b1;
          end
        end else begin : no_decode_amo // block: decode_amo
          // No match, keep decoder control signals IDLE
        end
      end

      default: begin
        // No match, keep decoder control signals IDLE
      end
    endcase

  end


endmodule : cv32e40x_a_decoder


