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
//                                                                            //
// Author:         Matthias Baer - baermatt@student.ethz.ch                   //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the mult module                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import uvm_pkg::*;

// Ensure only MUL, MULH, MULHSU, MULHU used (will only work if PULP_XPULP == 0)
a_mul_operator : assert property (@(posedge clk) disable iff (!rst_n) (enable_i)
  |-> (((operator_i == MUL_M32) && (op_c_i == 'b0)) || (operator_i == MUL_H)))
  else `uvm_error("controller", "Assertion a_mul_operator failed")

// check multiplication result for mulh
a_mulh_result : assert property (
  @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b11))
  |->
  (result_o == (($signed({{32{op_a_i[31]}}, op_a_i}) * $signed({{32{op_b_i[31]}}, op_b_i})) >>> 32) ) )
  else `uvm_error("controller", "Assertion a_mulh_result failed")

// check multiplication result for mulhsu
a_mulhsu_result : assert property (
  @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b01))
  |->
  (result_o == (($signed({{32{op_a_i[31]}}, op_a_i}) * {32'b0, op_b_i}) >> 32) ) )
  else `uvm_error("controller", "Assertion a_mulh_result failed")

// check multiplication result for mulhu
a_mulhu_result : assert property (
  @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b00))
  |->
  (result_o == (({32'b0, op_a_i} * {32'b0, op_b_i}) >> 32) ) )
  else `uvm_error("controller", "Assertion a_mulh_result failed")
