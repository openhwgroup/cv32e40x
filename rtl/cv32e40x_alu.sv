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
  input  logic              clk,
  input  logic              rst_n,
  input  alu_opcode_e       operator_i,
  input  logic [31:0]       operand_a_i,
  input  logic [31:0]       operand_b_i,

  output logic [31:0]       result_o,
  output logic              comparison_result_o,

  // Divider interface towards CLZ
  input logic               div_clz_en_i,
  input logic [31:0]        div_clz_data_i,
  output logic [5:0]        div_clz_result_o,

  // Divider interface towards shifter
  input logic               div_shift_en_i,
  input logic [5:0]         div_shift_amt_i,
  output logic [31:0]       div_op_a_shifted_o
);

  logic [31:0] operand_a_rev;
  
  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 32; k++)
    begin : gen_operand_a_rev
      assign operand_a_rev[k] = operand_a_i[31-k];
    end
  endgenerate

  logic [31:0] operand_b_neg;

  assign operand_b_neg = ~operand_b_i;


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
*/

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

  logic din_insn30, din_insn29, din_insn27, din_insn26, din_insn14;

  logic [31:0] shifter_x;
  logic [63:0] shifter_tmp;
  logic        shifter_zbsmode;
//logic        bfpmode;
  logic [31:0] shifter_result;
  logic [63:0] shifter_aa, shifter_bb;
  logic [5:0]  shifter_shamt; // Shift amount

  assign div_op_a_shifted_o = shifter_result;//shift_left_result;

  // BFP
  // wire [15:0] bfp_config = din_rs2[31:16];
  // wire [5:0]  bfp_len = {!bfp_config[11:8], bfp_config[11:8]};
  // wire [5:0]  bfp_off = bfp_config[4:0];
  // wire [31:0] bfp_mask = 32'h FFFFFFFF << bfp_len;

  always_comb begin
    case (operator_i)
      ALU_SLL: begin
        din_insn30 = 1'b0;
        din_insn29 = 1'b0;
        din_insn27 = 1'b0;
        din_insn26 = 1'b0;
        din_insn14 = 1'b0;
      end
      ALU_SRL: begin
        din_insn30 = 1'b0;
        din_insn29 = 1'b0;
        din_insn27 = 1'b0;
        din_insn26 = 1'b0;
        din_insn14 = 1'b1;
      end
      ALU_SRA: begin
        din_insn30 = 1'b1;
        din_insn29 = 1'b0;
        din_insn27 = 1'b0;
        din_insn26 = 1'b0;
        din_insn14 = 1'b1;
      end
//      ALU_SLO: begin
//        din_insn30 = 1'b0;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b0;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b0;
//      end
//      ALU_SRO: begin
//        din_insn30 = 1'b0;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b0;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b1;
//      end
//      ALU_ROL: begin
//        din_insn30 = 1'b1;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b0;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b0;
//      end
//      ALU_ROR: begin
//        din_insn30 = 1'b1;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b0;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b1;
//      end
//      ALU_B_BSET: begin
//        din_insn30 = 1'b0;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b1;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b0;
//      end
//      ALU_B_BCLR: begin
//        din_insn30 = 1'b1;
//        din_insn29 = 1'b0;
//        din_insn27 = 1'b1;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b0;
//      end
//      ALU_B_BINV: begin
//        din_insn30 = 1'b1;
//        din_insn29 = 1'b1;
//        din_insn27 = 1'b1;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b0;
//      end
//      ALU_B_BEXT: begin
//        din_insn30 = 1'b1;
//        din_insn29 = 1'b0;
//        din_insn27 = 1'b1;
//        din_insn26 = 1'b0;
//        din_insn14 = 1'b1;
//      end
      // FSL, FSR, BFP not addded
      default: begin
        din_insn30 = 1'b0;
        din_insn29 = 1'b0;
        din_insn27 = 1'b0;
        din_insn26 = 1'b0;
        din_insn14 = 1'b0;
      end
    endcase // case (operator_i)

    if (div_shift_en_i) begin
      din_insn30 = 1'b0;
      din_insn29 = 1'b0;
      din_insn27 = 1'b0;
      din_insn26 = 1'b0;
      din_insn14 = 1'b0;
    end
  end


//  assign bfpmode = 1'b0; //(operator_i == ALU_B_BFP);
  assign shifter_zbsmode  = (din_insn30 || din_insn29) && din_insn27 && !din_insn26;
  assign fsmode  = 1'b0; // (operator_i == ALU_B_FSL) ||
                         // (operator_i == ALU_B_FSR);

        always_comb begin
                shifter_shamt = div_shift_en_i ? div_shift_amt_i[5:0] : operand_b_i[5:0];
                shifter_aa = operand_a_i;
                shifter_bb = operand_b_i;

                if (!din_insn26) begin
                    // Shift amount up to 31 for non-funnel shifts
                    shifter_shamt[5] = 1'b0;
                end

                if (din_insn14) begin // Reverse bit order
                   // Treat right shifts as left shifts with corrected shift amount
                   shifter_shamt = -shifter_shamt;
                end

                if (!din_insn26) begin
                  casez ({din_insn30, din_insn29})
                    2'b 0z: shifter_bb = {64{din_insn29}};
                    2'b 10: shifter_bb = {64{operand_a_i[31]}};
                    2'b 11: shifter_bb = operand_a_i;
                  endcase
                  if (shifter_zbsmode && !din_insn14) begin
                    shifter_aa = 1;
                    shifter_bb = 0;
                  end
                end

                //if (bfpmode) begin
                //        aa = {32'h 0000_0000, ~bfp_mask};
                //        bb = 0;
                //        shamt = bfp_off;
                //end
        end

        always_comb begin
                shifter_result = shifter_x;
                if (shifter_zbsmode) begin
                        casez ({din_insn30, din_insn29, din_insn14})
                                3'b zz1: shifter_result =           1 &  shifter_x;
                                3'b 0zz: shifter_result = operand_a_i |  shifter_x;
                                3'b z0z: shifter_result = operand_a_i & ~shifter_x;
                                3'b 11z: shifter_result = operand_a_i ^  shifter_x;
                        endcase
                end
                //if (bfpmode)
                //        shifter_result = (A & ~shifter_x) | {32'b0, din_rs2[31:0] & ~bfp_mask} << bfp_off;
        end

        always_comb begin
                shifter_tmp = {shifter_bb[31:0], shifter_aa[31:0]};
                shifter_tmp = shifter_shamt[5] ? {shifter_tmp[31:0], shifter_tmp[63:32]} : shifter_tmp;
                shifter_tmp = shifter_shamt[4] ? {shifter_tmp[47:0], shifter_tmp[63:48]} : shifter_tmp;
                shifter_tmp = shifter_shamt[3] ? {shifter_tmp[55:0], shifter_tmp[63:56]} : shifter_tmp;
                shifter_tmp = shifter_shamt[2] ? {shifter_tmp[59:0], shifter_tmp[63:60]} : shifter_tmp;
                shifter_tmp = shifter_shamt[1] ? {shifter_tmp[61:0], shifter_tmp[63:62]} : shifter_tmp;
                shifter_tmp = shifter_shamt[0] ? {shifter_tmp[62:0], shifter_tmp[63:63]} : shifter_tmp;
        end

        assign shifter_x = shifter_tmp[31:0];






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

  
  logic [31:0] div_clz_data_rev;
  logic [4:0]  ff1_result; // holds the index of the first '1'
  logic        ff_no_one;  // if no ones are found
  
  generate
    genvar l;
    for(l = 0; l < 32; l++)
    begin : gen_div_clz_data_rev
      assign div_clz_data_rev[l] = div_clz_data_i[31-l];
    end
  endgenerate
  
  cv32e40x_ff_one ff_one_i
  (
    .in_i        ( div_clz_data_rev ),
    .first_one_o ( ff1_result ),
    .no_ones_o   ( ff_no_one  )
  );

  // Divider assumes CLZ returning 32 when there are no zeros (as per CLZ spec)
  assign div_clz_result_o = ff_no_one ? 6'd32 : ff1_result;
 

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
      ALU_SRL, ALU_SRA:  result_o = shifter_result;

      // Non-vector comparisons
      ALU_SLTS,  ALU_SLTU: result_o = {31'b0, comparison_result_o};

      // RV32B Zca instructions
      // TODO:OE: Investigate sharing ALU adder and shifter
      ALU_B_SH1ADD: result_o = (operand_a_i << 1) + operand_b_i;
      ALU_B_SH2ADD: result_o = (operand_a_i << 2) + operand_b_i;
      ALU_B_SH3ADD: result_o = (operand_a_i << 3) + operand_b_i;

      default: ; // default case to suppress unique warning
    endcase
  end

endmodule // cv32e40x_alu
