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
#(  
  parameter bit A_EXT     = 1'b0
)
(
  input logic           clk,
  input logic           rst_n,
  input decoder_ctrl_t  decoder_m_ctrl,
  input decoder_ctrl_t  decoder_a_ctrl,
  input decoder_ctrl_t  decoder_i_ctrl,
  input decoder_ctrl_t  decoder_b_ctrl,
  input decoder_ctrl_t  decoder_ctrl_mux,
  input logic [31:0]    instr_rdata_i
);

  // Check sub decoders have their outputs idle when there is no instruction match
  property p_idle_dec(decoder_ctrl_t dec_ctrl);
    @(posedge clk) disable iff (!rst_n)
      (dec_ctrl.illegal_insn |-> dec_ctrl == DECODER_CTRL_ILLEGAL_INSN);
  endproperty

  a_m_dec_idle : assert property(p_idle_dec(decoder_m_ctrl)) else `uvm_error("decoder", "Assertion a_m_dec_idle failed")
  a_a_dec_idle : assert property(p_idle_dec(decoder_a_ctrl)) else `uvm_error("decoder", "Assertion a_a_dec_idle failed")
  a_i_dec_idle : assert property(p_idle_dec(decoder_i_ctrl)) else `uvm_error("decoder", "Assertion a_i_dec_idle failed")
  a_b_dec_idle : assert property(p_idle_dec(decoder_b_ctrl)) else `uvm_error("decoder", "Assertion a_b_dec_idle failed")
  
  // Check that the two LSB of the incoming instructions word is always 2'b11
  // Predecoder should always emit uncompressed instructions
  property p_uncompressed_lsb;
    @(posedge clk) disable iff(!rst_n)
      (instr_rdata_i[1:0] == 2'b11);
  endproperty

  a_uncompressed_lsb: assert property(p_uncompressed_lsb) else `uvm_error("decoder", "2 LSBs not 2'b11")

  generate
    if (!A_EXT) begin : gen_no_a_extension_assertions
      // Check that A extension opcodes are decoded as illegal when A extension not enabled
      a_illegal_0 :
        assert property (@(posedge clk) disable iff (!rst_n)
          (instr_rdata_i[6:0] == OPCODE_AMO) |-> (decoder_ctrl_mux.illegal_insn == 'b1))
        else `uvm_error("decoder", "AMO instruction should be illegal")
    end
  endgenerate

  // Ensure that the A operand is only used for certain functional units
  a_alu_op_a_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (decoder_ctrl_mux.alu_op_a_mux_sel != OP_A_NONE)
                      |-> (
                      (
                        decoder_ctrl_mux.alu_en || decoder_ctrl_mux.div_en ||
                        decoder_ctrl_mux.csr_en || decoder_ctrl_mux.lsu_en
                      ) && !(decoder_ctrl_mux.mul_en || decoder_ctrl_mux.sys_en))
                    )
      else `uvm_error("decoder", "Unexpected A operand usage")

  // Ensure that the B operand is only used for certain functional units
  a_alu_op_b_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (decoder_ctrl_mux.alu_op_b_mux_sel != OP_B_NONE)
                      |-> (
                      (
                        decoder_ctrl_mux.alu_en || decoder_ctrl_mux.div_en ||
                        decoder_ctrl_mux.csr_en || decoder_ctrl_mux.lsu_en
                      ) && !(decoder_ctrl_mux.mul_en || decoder_ctrl_mux.sys_en))
                    )
      else `uvm_error("decoder", "Unexpected B operand usage")

  // Ensure that the C operand is only used for certain functional units
  a_op_c_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (decoder_ctrl_mux.op_c_mux_sel != OP_C_NONE)
                      |-> ((decoder_ctrl_mux.alu_en || (decoder_ctrl_mux.lsu_en && decoder_ctrl_mux.lsu_we))))
      else `uvm_error("decoder", "Unexpected C operand usage")

  // Ensure that functional unit enables are one-hot (including illegal)
  a_functional_unit_enable_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot({decoder_ctrl_mux.alu_en, decoder_ctrl_mux.div_en, decoder_ctrl_mux.mul_en,
                              decoder_ctrl_mux.csr_en, decoder_ctrl_mux.sys_en, decoder_ctrl_mux.lsu_en,
                              decoder_ctrl_mux.illegal_insn}))
      else `uvm_error("decoder", "Multiple functional units enabled")

endmodule : cv32e40x_decoder_sva
