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
//                                                                            //
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    RTL assertions decoder module                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
  
module cv32e40x_decoder_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  (
   input logic clk,
   input logic rst_n,
   input decoder_ctrl_t decoder_i_ctrl,
   input decoder_ctrl_t decoder_m_ctrl,
   input decoder_ctrl_t decoder_a_ctrl,
   input logic [31:0] instr_rdata_i
   );

  
  // Check sub decoders have their outputs idle when there's no instruction match
  property p_idle_dec(decoder_ctrl_t dec_ctrl);
    @(posedge clk) disable iff (!rst_n)
      (dec_ctrl.illegal_insn |-> dec_ctrl == DECODER_CTRL_ILLEGAL_INSN);
  endproperty

  a_m_dec_idle : assert property(p_idle_dec(decoder_m_ctrl)) else `uvm_error("decoder", "Assertion a_m_dec_idle failed")
  a_a_dec_idle : assert property(p_idle_dec(decoder_a_ctrl)) else `uvm_error("decoder", "Assertion a_a_dec_idle failed")
  a_i_dec_idle : assert property(p_idle_dec(decoder_i_ctrl)) else `uvm_error("decoder", "Assertion a_i_dec_idle failed")
  
  // Check that the two LSB of the incoming instructions word is always 2'b11
  // Predecoder should always emit uncompressed instructions
  property p_uncompressed_lsb;
    @(posedge clk) disable iff(!rst_n)
      (instr_rdata_i[1:0] == 2'b11);
  endproperty

  a_uncompressed_lsb: assert property(p_uncompressed_lsb) else `uvm_error("decoder", "2LSB not 2'b11")

endmodule : cv32e40x_decoder_sva


