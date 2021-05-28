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
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    ALU                                                        //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Arithmetic logic unit of the pipelined processor           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_alu import cv32e40x_pkg::*;
(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic                     enable_i,
  input  alu_opcode_e              operator_i,
  input  logic [31:0]              operand_a_i,
  input  logic [31:0]              operand_b_i,

  output logic [31:0]              result_o,
  output logic                     comparison_result_o,

  output logic                     ready_o,
  input  logic                     ex_ready_i
);

  logic [31:0] operand_a_rev;
  logic [31:0] operand_a_neg;
  logic [31:0] operand_a_neg_rev;

  assign operand_a_neg = ~operand_a_i;

  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 32; k++)
    begin : gen_operand_a_rev
      assign operand_a_rev[k] = operand_a_i[31-k];
    end
  endgenerate

  // bit reverse operand_a_neg for left shifts and bit counting
  generate
    genvar m;
    for(m = 0; m < 32; m++)
    begin : gen_operand_a_neg_rev
      assign operand_a_neg_rev[m] = operand_a_neg[31-m];
    end
  endgenerate

  logic [31:0] operand_b_neg;

  assign operand_b_neg = ~operand_b_i;


  logic [5:0]  div_shift;
  logic        div_valid;

  //////////////////////////////////////////////////////////////////////////////////////////
  //   ____            _   _ _   _                      _      _       _     _            //
  //  |  _ \ __ _ _ __| |_(_) |_(_) ___  _ __   ___  __| |    / \   __| | __| | ___ _ __  //
  //  | |_) / _` | '__| __| | __| |/ _ \| '_ \ / _ \/ _` |   / _ \ / _` |/ _` |/ _ \ '__| //
  //  |  __/ (_| | |  | |_| | |_| | (_) | | | |  __/ (_| |  / ___ \ (_| | (_| |  __/ |    //
  //  |_|   \__,_|_|   \__|_|\__|_|\___/|_| |_|\___|\__,_| /_/   \_\__,_|\__,_|\___|_|    //
  //                                                                                      //
  //////////////////////////////////////////////////////////////////////////////////////////

  logic        adder_op_b_negate;
  logic [31:0] adder_op_a, adder_op_b;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;
  logic [33:0] adder_result_expanded;

  assign adder_op_b_negate = (operator_i == ALU_SUB);

  // prepare operand a
  assign adder_op_a = operand_a_i;

  // prepare operand b
  assign adder_op_b = adder_op_b_negate ? operand_b_neg : operand_b_i;

  // prepare carry
  assign adder_in_a = {adder_op_a, 1'b1};
  assign adder_in_b = {adder_op_b, adder_op_b_negate};

  // actual adder
  assign adder_result_expanded = $unsigned(adder_in_a) + $unsigned(adder_in_b);
  assign adder_result = adder_result_expanded[32:1];


  ////////////////////////////////////////
  //  ____  _   _ ___ _____ _____       //
  // / ___|| | | |_ _|  ___|_   _|      //
  // \___ \| |_| || || |_    | |        //
  //  ___) |  _  || ||  _|   | |        //
  // |____/|_| |_|___|_|     |_|        //
  //                                    //
  ////////////////////////////////////////

  logic        shift_left;         // should we shift left
  logic        shift_arithmetic;

  logic  [4:0] shift_amt;          // amount of shift used for the actual shifter
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;

  // shifter is also used for preparing operand for division
  assign shift_amt = div_valid ? div_shift[4:0] : operand_b_i[4:0];

  assign shift_left = (operator_i == ALU_SLL) ||
                      (operator_i == ALU_DIV) || (operator_i == ALU_DIVU) ||
                      (operator_i == ALU_REM) || (operator_i == ALU_REMU);

  assign shift_arithmetic = (operator_i == ALU_SRA) ||
                            (operator_i == ALU_ADD) || (operator_i == ALU_SUB);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev : operand_a_i;

  // right shifts, we let the synthesizer optimize this
  logic [63:0] shift_op_a_32;

  assign shift_op_a_32 = $signed({ {32{shift_arithmetic & shift_op_a[31]}}, shift_op_a});

  assign shift_right_result = shift_op_a_32 >> shift_amt;

  // bit reverse the shift_right_result for left shifts
  genvar       j;
  generate
    for(j = 0; j < 32; j++)
    begin : gen_shift_left_result
      assign shift_left_result[j] = shift_right_result[31-j];
    end
  endgenerate

  assign shift_result = shift_left ? shift_left_result : shift_right_result;


/*

 // New shifter based on https://github.com/riscv/riscv-bitmanip/blob/main-history/verilog/rvb_shifter/rvb_shifter.v 

 *  Copyright (C) 2019  Claire Wolf <claire@symbioticeda.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *



        // 30 29 27 26 14 13  3   Function
        // --------------------   --------
        //  0  0  0  0  0  0  W   SLL
        //  0  0  0  0  1  0  W   SRL
        //  1  0  0  0  1  0  W   SRA
        //  0  1  0  0  0  0  W   SLO
        //  0  1  0  0  1  0  W   SRO
        //  1  1  0  0  0  0  W   ROL
        //  1  1  0  0  1  0  W   ROR
        // --------------------   --------
        //  -  -  -  1  0  0  W   FSL
        //  -  -  -  1  1  0  W   FSR
        // --------------------   --------
        //  0  1  1  0  0  0  W   SBSET
        //  1  0  1  0  0  0  W   SBCLR
        //  1  1  1  0  0  0  W   SBINV
        //  1  0  1  0  1  0  W   SBEXT
        // --------------------   --------
        //  1  0  1  0  1  1  W   BFP

        reg [63:0] tmp;

        wire sbmode = SBOP && (din_insn30 || din_insn29) && din_insn27 && !din_insn26;
        wire bfpmode = BFP && din_insn13;

        reg [63:0] Y;
        wire [63:0] A, B, X;
        assign A = din_rs1;
        assign B = din_rs3;
        assign dout_rd = Y[31:0];

        reg [63:0] aa, bb;
        reg [5:0] shamt;

        wire [15:0] bfp_config = din_rs2[31:16];

        wire [5:0] bfp_len = {!bfp_config[11:8], bfp_config[11:8]};
        wire [5:0] bfp_off = bfp_config[4:0];
        wire [31:0] bfp_mask = 32'h FFFFFFFF << bfp_len;

        always @* begin
                shamt = din_rs2[5:0];
                aa = A;
                bb = B;

                if (!din_insn26) begin
                    // Shift amount up to 31 for non-funnel shifts
                    shamt[5] = 0;
                end

                if (din_insn14) begin
                   // Treat right shifts as left shifts with corrected shift amount
                   shamt = -shamt;
                end

                if (!din_insn26) begin
                        casez ({din_insn30, din_insn29})
                                2'b 0z: bb = {64{din_insn29}};
                                2'b 10: bb = {64{A[31]}};
                                2'b 11: bb = A;
                        endcase
                        if (sbmode && !din_insn14) begin
                                aa = 1;
                                bb = 0;
                        end
                end

                if (bfpmode) begin
                        aa = {32'h 0000_0000, ~bfp_mask};
                        bb = 0;
                        shamt = bfp_off;
                end
        end

        always @* begin
                Y = X;
                if (sbmode) begin
                        casez ({din_insn30, din_insn29, din_insn14})
                                3'b zz1: Y = 1 &  X;
                                3'b 0zz: Y = A |  X;
                                3'b z0z: Y = A & ~X;
                                3'b 11z: Y = A ^  X;
                        endcase
                end
                if (bfpmode)
                        Y = (A & ~X) | {32'b0, din_rs2[31:0] & ~bfp_mask} << bfp_off;
        end

        always @* begin
                tmp = {bb[31:0], aa[31:0]};
                tmp = shamt[5] ? {tmp[31:0], tmp[63:32]} : tmp;
                tmp = shamt[4] ? {tmp[47:0], tmp[63:48]} : tmp;
                tmp = shamt[3] ? {tmp[55:0], tmp[63:56]} : tmp;
                tmp = shamt[2] ? {tmp[59:0], tmp[63:60]} : tmp;
                tmp = shamt[1] ? {tmp[61:0], tmp[63:62]} : tmp;
                tmp = shamt[0] ? {tmp[62:0], tmp[63:63]} : tmp;
        end

        assign X = {32'bx, tmp[31:0]};


*/


  //////////////////////////////////////////////////////////////////
  //   ____ ___  __  __ ____   _    ____  ___ ____   ___  _   _   //
  //  / ___/ _ \|  \/  |  _ \ / \  |  _ \|_ _/ ___| / _ \| \ | |  //
  // | |  | | | | |\/| | |_) / _ \ | |_) || |\___ \| | | |  \| |  //
  // | |__| |_| | |  | |  __/ ___ \|  _ < | | ___) | |_| | |\  |  //
  //  \____\___/|_|  |_|_| /_/   \_\_| \_\___|____/ \___/|_| \_|  //
  //                                                              //
  //////////////////////////////////////////////////////////////////

  logic is_equal;
  logic is_greater;     // handles both signed and unsigned forms
  logic cmp_signed;

  assign cmp_signed = (operator_i == ALU_GES) || (operator_i == ALU_LTS) || (operator_i == ALU_SLTS);
  assign is_equal = (operand_a_i == operand_b_i);
  assign is_greater = $signed({operand_a_i[31] & cmp_signed, operand_a_i}) > $signed({operand_b_i[31] & cmp_signed, operand_b_i});

  // generate comparison result
  logic cmp_result;

  always_comb
  begin
    cmp_result = is_equal;
    unique case (operator_i)
      ALU_EQ:            cmp_result = is_equal;
      ALU_NE:            cmp_result = ~is_equal;
      ALU_GES, ALU_GEU:  cmp_result = is_greater | is_equal;
      ALU_LTS, ALU_SLTS,
      ALU_LTU, ALU_SLTU: cmp_result = ~(is_greater | is_equal);

      default: ;
    endcase
  end

  assign comparison_result_o = cmp_result;

  /////////////////////////////////////////////////////////////////////
  //   ____  _ _      ____                  _      ___               //
  //  | __ )(_) |_   / ___|___  _   _ _ __ | |_   / _ \ _ __  ___    //
  //  |  _ \| | __| | |   / _ \| | | | '_ \| __| | | | | '_ \/ __|   //
  //  | |_) | | |_  | |__| (_) | |_| | | | | |_  | |_| | |_) \__ \_  //
  //  |____/|_|\__|  \____\___/ \__,_|_| |_|\__|  \___/| .__/|___(_) //
  //                                                   |_|           //
  /////////////////////////////////////////////////////////////////////

  logic [31:0] ff_input;   // either op_a_i or its bit reversed version
  logic [5:0]  cnt_result; // population count
  logic [5:0]  clb_result; // count leading bits
  logic [4:0]  ff1_result; // holds the index of the first '1'
  logic        ff_no_one;  // if no ones are found

  cv32e40x_popcnt popcnt_i
  (
    .in_i        ( operand_a_i ),
    .result_o    ( cnt_result  )
  );

  always_comb
  begin
    ff_input = '0;

    case (operator_i)
      ALU_DIVU,
      ALU_REMU: ff_input = operand_a_rev;

      ALU_DIV,
      ALU_REM: begin
        if (operand_a_i[31])
          ff_input = operand_a_neg_rev;
        else
          ff_input = operand_a_rev;
      end
    endcase
  end

  cv32e40x_ff_one ff_one_i
  (
    .in_i        ( ff_input   ),
    .first_one_o ( ff1_result ),
    .no_ones_o   ( ff_no_one  )
  );

  // special case if ff1_res is 0 (no 1 found), then we keep the 0
  // this is done in the result mux
  assign clb_result  = ff1_result - 5'd1;
 
  ////////////////////////////////////////////////////
  //  ____ _____     __     __  ____  _____ __  __  //
  // |  _ \_ _\ \   / /    / / |  _ \| ____|  \/  | //
  // | | | | | \ \ / /    / /  | |_) |  _| | |\/| | //
  // | |_| | |  \ V /    / /   |  _ <| |___| |  | | //
  // |____/___|  \_/    /_/    |_| \_\_____|_|  |_| //
  //                                                //
  ////////////////////////////////////////////////////

   logic [31:0] result_div;
   logic        div_ready;
   logic        div_signed;
   logic        div_rem;
   logic        div_op_a_signed;
   logic [5:0]  div_shift_int;

   // Decode operator
   always_comb begin

     div_signed = 1'b0;
     div_rem    = 1'b0;
     div_valid  = 1'b0;

     unique case(operator_i)
       ALU_DIVU: begin
	       div_valid  = enable_i;
         div_signed = 1'b0;
         div_rem    = 1'b0;
       end
       ALU_DIV : begin
	       div_valid  = enable_i;
         div_signed = 1'b1;
         div_rem    = 1'b0;
       end
       ALU_REMU: begin
	       div_valid  = enable_i;
         div_signed = 1'b0;
         div_rem    = 1'b1;
       end
       ALU_REM : begin
	       div_valid  = enable_i;
         div_signed = 1'b1;
         div_rem    = 1'b1;
       end
       default: ; // default case to suppress unique warning
     endcase
   end

   assign div_op_a_signed = operand_a_i[31] & div_signed;
   assign div_shift_int = ff_no_one ? 6'd31 : clb_result;
   assign div_shift = div_shift_int + (div_op_a_signed ? 6'd0 : 6'd1);

   // inputs A and B are swapped
   cv32e40x_alu_div alu_div_i
     (
      .Clk_CI       ( clk               ),
      .Rst_RBI      ( rst_n             ),

      // input IF
      .OpA_DI       ( operand_b_i       ),
      .OpB_DI       ( shift_left_result ),
      .OpBShift_DI  ( div_shift         ),
      .OpBIsZero_SI ( (cnt_result == 0) ),

      .OpBSign_SI   ( div_op_a_signed   ),
      .DivSigned_SI ( div_signed        ),
      .DivRem_SI    ( div_rem           ),
      .Res_DO       ( result_div        ),

      // Hand-Shake
      .InVld_SI     ( div_valid         ),
      .OutRdy_SI    ( ex_ready_i        ),
      .OutVld_SO    ( div_ready         )
      );

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
    result_o   = '0;

    unique case (operator_i)
      // Standard Operations
      ALU_AND:  result_o = operand_a_i & operand_b_i;
      ALU_OR:   result_o = operand_a_i | operand_b_i;
      ALU_XOR:  result_o = operand_a_i ^ operand_b_i;

      // Adder Operations
      ALU_ADD,
      ALU_SUB : result_o = adder_result;

      // Shift Operations
      ALU_SLL,
      ALU_SRL, ALU_SRA:  result_o = shift_result;

      // Non-vector comparisons
      ALU_SLTS,  ALU_SLTU: result_o = {31'b0, comparison_result_o};

      // Division Unit Commands
      ALU_DIV, ALU_DIVU,
      ALU_REM, ALU_REMU: result_o = result_div;

      default: ; // default case to suppress unique warning
    endcase
  end

  assign ready_o = div_ready;

endmodule
