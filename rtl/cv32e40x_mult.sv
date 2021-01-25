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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Subword multiplier and MAC                                 //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Advanced MAC unit for PULP.                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_mult import cv32e40x_pkg::*;
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        enable_i,
  input  mul_opcode_e operator_i,

  // integer and short multiplier
  input  logic        short_subword_i,
  input  logic [ 1:0] short_signed_i,

  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] op_c_i,

  output logic [31:0] result_o,

  output logic        multicycle_o,
  output logic        ready_o,
  input  logic        ex_ready_i
);


  ///////////////////////////////////////////////////////////////
  //  ___ _  _ _____ ___ ___ ___ ___   __  __ _   _ _  _____   //
  // |_ _| \| |_   _| __/ __| __| _ \ |  \/  | | | | ||_   _|  //
  //  | || .  | | | | _| (_ | _||   / | |\/| | |_| | |__| |    //
  // |___|_|\_| |_| |___\___|___|_|_\ |_|  |_|\___/|____|_|    //
  //                                                           //
  ///////////////////////////////////////////////////////////////

  logic [16:0] short_op_a;
  logic [16:0] short_op_b;
  logic [32:0] short_op_c;
  logic [33:0] short_mul;
  logic [33:0] short_mac;
  logic [33:0] short_result;

  logic        short_mac_msb1;
  logic        short_mac_msb0;

  logic [ 4:0] short_imm;
  logic [ 1:0] short_subword;
  logic [ 1:0] short_signed;
  logic        short_shift_arith;
  logic [ 4:0] mulh_imm;
  logic [ 1:0] mulh_subword;
  logic [ 1:0] mulh_signed;
  logic        mulh_shift_arith;
  logic        mulh_carry_q;
  logic        mulh_active;
  logic        mulh_save;
  logic        mulh_clearcarry;
  logic        mulh_ready;

  mult_state_e mulh_CS, mulh_NS;

  // perform subword selection and sign extensions
  assign short_op_a[15:0] = short_subword[0] ? op_a_i[31:16] : op_a_i[15:0];
  assign short_op_b[15:0] = short_subword[1] ? op_b_i[31:16] : op_b_i[15:0];

  assign short_op_a[16]   = short_signed[0] & short_op_a[15];
  assign short_op_b[16]   = short_signed[1] & short_op_b[15];

  assign short_op_c       = mulh_active ? $signed({mulh_carry_q, op_c_i}) : $signed(op_c_i);

  assign short_mul        = $signed(short_op_a) * $signed(short_op_b);
  assign short_mac        = $signed(short_op_c) + $signed(short_mul);

   //we use only short_signed_i[0] as it cannot be short_signed_i[1] 1 and short_signed_i[0] 0
  assign short_result     = $signed({short_shift_arith & short_mac_msb1, short_shift_arith & short_mac_msb0, short_mac[31:0]}) >>> short_imm;

  // choose between normal short multiplication operation and mulh operation
  assign short_imm         = mulh_active ? mulh_imm         : 'd0;
  assign short_subword     = mulh_active ? mulh_subword     : {2{short_subword_i}};
  assign short_signed      = mulh_active ? mulh_signed      : short_signed_i;
  assign short_shift_arith = mulh_active ? mulh_shift_arith : short_signed_i[0];

  assign short_mac_msb1    = mulh_active ? short_mac[33] : short_mac[31];
  assign short_mac_msb0    = mulh_active ? short_mac[32] : short_mac[31];

  always_comb
  begin
    mulh_NS          = mulh_CS;
    mulh_imm         = 5'd0;
    mulh_subword     = 2'b00;
    mulh_signed      = 2'b00;
    mulh_shift_arith = 1'b0;
    mulh_ready       = 1'b0;
    mulh_active      = 1'b1;
    mulh_save        = 1'b0;
    mulh_clearcarry  = 1'b0;
    multicycle_o     = 1'b0;

    case (mulh_CS)
      IDLE_MULT: begin
        mulh_active = 1'b0;
        mulh_ready  = 1'b1;
        mulh_save   = 1'b0;
        if ((operator_i == MUL_H) && enable_i) begin
          mulh_ready  = 1'b0;
          mulh_NS     = STEP0;
        end
      end

      STEP0: begin
        multicycle_o = 1'b1;
        mulh_imm         = 5'd16;
        mulh_active      = 1'b1;
        //AL*BL never overflows
        mulh_save        = 1'b0;
        mulh_NS          = STEP1;
        //Here always a 32'b unsigned result (no carry)
      end

      STEP1: begin
        multicycle_o = 1'b1;
        //AL*BH is signed iff B is signed
        mulh_signed      = {short_signed_i[1], 1'b0};
        mulh_subword     = 2'b10;
        mulh_save        = 1'b1;
        mulh_shift_arith = 1'b1;
        mulh_NS          = STEP2;
        //Here signed 32'b + unsigned 32'b result.
        //Result is a signed 33'b
        //Store the carry as it will be used as sign extension, we do
        //not shift
      end

      STEP2: begin
        multicycle_o = 1'b1;
        //AH*BL is signed iff A is signed
        mulh_signed      = {1'b0, short_signed_i[0]};
        mulh_subword     = 2'b01;
        mulh_imm         = 5'd16;
        mulh_save        = 1'b1;
        mulh_clearcarry  = 1'b1;
        mulh_shift_arith = 1'b1;
        mulh_NS          = FINISH;
        //Here signed 32'b + signed 33'b result.
        //Result is a signed 34'b
        //We do not store the carries as the bits 34:33 are shifted back, so we clear it
      end

      FINISH: begin
        mulh_signed  = short_signed_i;
        mulh_subword = 2'b11;
        mulh_ready   = 1'b1;
        if (ex_ready_i)
          mulh_NS = IDLE_MULT;
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n)
    begin
      mulh_CS      <= IDLE_MULT;
      mulh_carry_q <= 1'b0;
    end else begin
      mulh_CS      <= mulh_NS;

      if (mulh_save)
        mulh_carry_q <= ~mulh_clearcarry & short_mac[32];
      else if (ex_ready_i) // clear carry when we are going to the next instruction
        mulh_carry_q <= 1'b0;
    end
  end

  // 32x32 = 32-bit multiplier
  logic [31:0] int_result;

  assign int_result = $signed(op_a_i) * $signed(op_b_i);

  ////////////////////////////////////////////////////////
  //   ____                 _ _     __  __              //
  //  |  _ \ ___  ___ _   _| | |_  |  \/  |_   ___  __  //
  //  | |_) / _ \/ __| | | | | __| | |\/| | | | \ \/ /  //
  //  |  _ <  __/\__ \ |_| | | |_  | |  | | |_| |>  <   //
  //  |_| \_\___||___/\__,_|_|\__| |_|  |_|\__,_/_/\_\  //
  //                                                    //
  ////////////////////////////////////////////////////////

  always_comb
  begin
    if (operator_i == MUL_M32) begin
      result_o = int_result[31:0];
    end else begin
      result_o = short_result[31:0];
    end
  end

  assign ready_o = mulh_ready;

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

   // Ensure only MUL, MULH, MULHSU, MULHU used (will only work if PULP_XPULP == 0)
   a_mul_operator : assert property (@(posedge clk) disable iff (!rst_n) (enable_i)
   |-> (((operator_i == MUL_M32) && (op_c_i == 'b0)) || (operator_i == MUL_H)));

  
  // check multiplication result for mulh
  assert property (
    @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b11))
    |->
    (result_o == (($signed({{32{op_a_i[31]}}, op_a_i}) * $signed({{32{op_b_i[31]}}, op_b_i})) >>> 32) ) );

  // check multiplication result for mulhsu
  assert property (
    @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b01))
    |->
    (result_o == (($signed({{32{op_a_i[31]}}, op_a_i}) * {32'b0, op_b_i}) >> 32) ) );

  // check multiplication result for mulhu
  assert property (
    @(posedge clk) ((mulh_CS == FINISH) && (operator_i == MUL_H) && (short_signed_i == 2'b00))
    |->
    (result_o == (({32'b0, op_a_i} * {32'b0, op_b_i}) >> 32) ) );

`endif

endmodule
