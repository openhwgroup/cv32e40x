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

  logic [ 4:0] mulh_imm;
  logic [ 1:0] mulh_subword;
  logic [ 1:0] mulh_signed;
  logic        mulh_shift_arith;
  logic        mulh_carry_q;
  logic        mulh_save;
  logic        mulh_clearcarry;

  mult_state_e mulh_state, mulh_state_next;

  // perform subword selection and sign extensions
  assign short_op_a[15:0] = mulh_subword[0] ? op_a_i[31:16] : op_a_i[15:0];
  assign short_op_b[15:0] = mulh_subword[1] ? op_b_i[31:16] : op_b_i[15:0];

  assign short_op_a[16]   = mulh_signed[0] & short_op_a[15];
  assign short_op_b[16]   = mulh_signed[1] & short_op_b[15];

  assign short_op_c       = $signed({mulh_carry_q, op_c_i});

  assign short_mul        = $signed(short_op_a) * $signed(short_op_b);
  assign short_mac        = $signed(short_op_c) + $signed(short_mul);

   //we use only short_signed_i[0] as it cannot be short_signed_i[1] 1 and short_signed_i[0] 0
  assign short_result     = $signed({mulh_shift_arith & short_mac_msb1, mulh_shift_arith & short_mac_msb0, short_mac[31:0]}) >>> mulh_imm;

  // choose between normal short multiplication operation and mulh operation

  assign short_mac_msb1    = short_mac[33];
  assign short_mac_msb0    = short_mac[32];

  always_comb
  begin
    mulh_state_next  = mulh_state;
    mulh_imm         = 5'd0;
    mulh_subword     = 2'b00;
    mulh_signed      = 2'b00;
    mulh_shift_arith = 1'b0;
    mulh_save        = 1'b0;
    mulh_clearcarry  = 1'b0;
    multicycle_o     = 1'b0;

    case (mulh_state)
      ALBL: begin
        if ((operator_i == MUL_H) && enable_i) begin
          multicycle_o    = 1'b1;
          mulh_imm        = 5'd16;
          mulh_state_next = ALBH;
        end
      end

      ALBH: begin
        multicycle_o     = 1'b1;
        //AL*BH is signed if B is signed
        mulh_signed      = {short_signed_i[1], 1'b0};
        mulh_subword     = 2'b10;
        mulh_save        = 1'b1;
        mulh_shift_arith = 1'b1;
        mulh_state_next  = AHBL;
        //Here signed 32'b + unsigned 32'b result.
        //Result is a signed 33'b
        //Store the carry as it will be used as sign extension, we do
        //not shift
      end

      AHBL: begin
        multicycle_o     = 1'b1;
        //AH*BL is signed if A is signed
        mulh_signed      = {1'b0, short_signed_i[0]};
        mulh_subword     = 2'b01;
        mulh_imm         = 5'd16;
        mulh_save        = 1'b1;
        mulh_clearcarry  = 1'b1;
        mulh_shift_arith = 1'b1;
        mulh_state_next  = AHBH;
        //Here signed 32'b + signed 33'b result.
        //Result is a signed 34'b
        //We do not store the carries as the bits 34:33 are shifted back, so we clear it
      end

      AHBH: begin
        mulh_signed  = short_signed_i;
        mulh_subword = 2'b11;
        if (ex_ready_i)
          mulh_state_next = ALBL;
      end
      default: ;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n)
    begin
      mulh_state      <= ALBL;
      mulh_carry_q <= 1'b0;
    end else begin
      mulh_state      <= mulh_state_next;

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

  assign ready_o = !multicycle_o;

endmodule
