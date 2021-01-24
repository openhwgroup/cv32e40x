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
  
  input id_ex_pipe_t               id_ex_pipe_i,

  output logic [31:0]              result_o,
  output logic                     comparison_result_o,

  output logic                     ready_o,
  input  logic                     ex_ready_i
);

  logic [31:0] operand_a_rev;
  logic [31:0] operand_a_neg;
  logic [31:0] operand_a_neg_rev;

  assign operand_a_neg = ~id_ex_pipe_i.alu_operand_a;

  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 32; k++)
    begin : gen_operand_a_rev
      assign operand_a_rev[k] = id_ex_pipe_i.alu_operand_a[31-k];
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

  assign operand_b_neg = ~id_ex_pipe_i.alu_operand_b;


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

  assign adder_op_b_negate = (id_ex_pipe_i.alu_operator == ALU_SUB);

  // prepare operand a
  assign adder_op_a = id_ex_pipe_i.alu_operand_a;

  // prepare operand b
  assign adder_op_b = adder_op_b_negate ? operand_b_neg : id_ex_pipe_i.alu_operand_b;

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
  logic        shift_use_round;
  logic        shift_arithmetic;

  logic [31:0] shift_amt_left;     // amount of shift, if to the left
  logic [31:0] shift_amt;          // amount of shift, to the right
  logic [31:0] shift_amt_int;      // amount of shift, used for the actual shifters
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;

  // shifter is also used for preparing operand for division
  assign shift_amt = div_valid ? div_shift : id_ex_pipe_i.alu_operand_b;

  // by reversing the bits of the input, we also have to reverse the order of shift amounts
  assign shift_amt_left[31:0] = shift_amt[31:0];

  assign shift_left = (id_ex_pipe_i.alu_operator == ALU_SLL) ||
                      (id_ex_pipe_i.alu_operator == ALU_DIV) || (id_ex_pipe_i.alu_operator == ALU_DIVU) ||
                      (id_ex_pipe_i.alu_operator == ALU_REM) || (id_ex_pipe_i.alu_operator == ALU_REMU);

  assign shift_use_round = (id_ex_pipe_i.alu_operator == ALU_ADD) || (id_ex_pipe_i.alu_operator == ALU_SUB);

  assign shift_arithmetic = (id_ex_pipe_i.alu_operator == ALU_SRA) ||
                            (id_ex_pipe_i.alu_operator == ALU_ADD) || (id_ex_pipe_i.alu_operator == ALU_SUB);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev :
                          (shift_use_round ? adder_result : id_ex_pipe_i.alu_operand_a);
  assign shift_amt_int = shift_use_round ? 32'b0 :
                          (shift_left ? shift_amt_left : shift_amt);

  // right shifts, we let the synthesizer optimize this
  logic [63:0] shift_op_a_32;

  assign shift_op_a_32 = $signed({ {32{shift_arithmetic & shift_op_a[31]}}, shift_op_a});

  assign shift_right_result = shift_op_a_32 >> shift_amt_int[4:0];

  // bit reverse the shift_right_result for left shifts
  genvar       j;
  generate
    for(j = 0; j < 32; j++)
    begin : gen_shift_left_result
      assign shift_left_result[j] = shift_right_result[31-j];
    end
  endgenerate

  assign shift_result = shift_left ? shift_left_result : shift_right_result;


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

  always_comb
  begin
    cmp_signed = 1'b0;

    unique case (id_ex_pipe_i.alu_operator)
      ALU_GES,
      ALU_LTS,
      ALU_SLTS: begin
        cmp_signed = 1'b1;
      end

      default:;
    endcase
  end

  assign is_equal = (id_ex_pipe_i.alu_operand_a == id_ex_pipe_i.alu_operand_b);
  assign is_greater = $signed({id_ex_pipe_i.alu_operand_a[31] & cmp_signed, id_ex_pipe_i.alu_operand_a}) > $signed({id_ex_pipe_i.alu_operand_b[31] & cmp_signed, id_ex_pipe_i.alu_operand_b});

  // generate comparison result
  logic cmp_result;

  always_comb
  begin
    cmp_result = is_equal;
    unique case (id_ex_pipe_i.alu_operator)
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
    .in_i        ( id_ex_pipe_i.alu_operand_a ),
    .result_o    ( cnt_result                 )
  );

  always_comb
  begin
    ff_input = '0;

    case (id_ex_pipe_i.alu_operator)
      ALU_DIVU,
      ALU_REMU: ff_input = operand_a_rev;

      ALU_DIV,
      ALU_REM: begin
        if (id_ex_pipe_i.alu_operand_a[31])
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
   logic        div_op_a_signed;
   logic [5:0]  div_shift_int;

   assign div_signed = id_ex_pipe_i.alu_operator[0];

   assign div_op_a_signed = id_ex_pipe_i.alu_operand_a[31] & div_signed;

   assign div_shift_int = ff_no_one ? 6'd31 : clb_result;
   assign div_shift = div_shift_int + (div_op_a_signed ? 6'd0 : 6'd1);

   assign div_valid = id_ex_pipe_i.alu_en & ((id_ex_pipe_i.alu_operator == ALU_DIV) || (id_ex_pipe_i.alu_operator == ALU_DIVU) ||
                      (id_ex_pipe_i.alu_operator == ALU_REM) || (id_ex_pipe_i.alu_operator == ALU_REMU));

   // inputs A and B are swapped
   cv32e40x_alu_div alu_div_i
     (
      .Clk_CI       ( clk                            ),
      .Rst_RBI      ( rst_n                          ),

      // input IF
      .OpA_DI       ( id_ex_pipe_i.alu_operand_b     ),
      .OpB_DI       ( shift_left_result              ),
      .OpBShift_DI  ( div_shift                      ),
      .OpBIsZero_SI ( (cnt_result == 0)              ),

      .OpBSign_SI   ( div_op_a_signed                ),
      .OpCode_SI    ( id_ex_pipe_i.alu_operator[1:0] ), // todo: this should not depend on encoding like this: instead change divider to have two inputs, e.g. unsigned, rem

      .Res_DO       ( result_div                     ),

      // Hand-Shake
      .InVld_SI     ( div_valid                      ),
      .OutRdy_SI    ( ex_ready_i                     ),
      .OutVld_SO    ( div_ready                      )
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

    unique case (id_ex_pipe_i.alu_operator)
      // Standard Operations
      ALU_AND:  result_o = id_ex_pipe_i.alu_operand_a & id_ex_pipe_i.alu_operand_b;
      ALU_OR:   result_o = id_ex_pipe_i.alu_operand_a | id_ex_pipe_i.alu_operand_b;
      ALU_XOR:  result_o = id_ex_pipe_i.alu_operand_a ^ id_ex_pipe_i.alu_operand_b;

      // Shift Operations
      ALU_ADD,
      ALU_SUB,
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

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

    // Check that no PULP_XPULP features are used

    // Check that certain ALU operations are not used when PULP extension is not enabled
    a_alu_operator_0 : assert property (@(posedge clk) disable iff (!rst_n) (1'b1)
    |-> ((id_ex_pipe_i.alu_operator != ALU_ADDU ) && (id_ex_pipe_i.alu_operator != ALU_SUBU ) &&
         (id_ex_pipe_i.alu_operator != ALU_ADDR ) && (id_ex_pipe_i.alu_operator != ALU_SUBR ) &&
         (id_ex_pipe_i.alu_operator != ALU_ADDUR) && (id_ex_pipe_i.alu_operator != ALU_SUBUR) &&
         (id_ex_pipe_i.alu_operator != ALU_ROR) && (id_ex_pipe_i.alu_operator != ALU_BEXT) &&
         (id_ex_pipe_i.alu_operator != ALU_BEXTU) && (id_ex_pipe_i.alu_operator != ALU_BINS) &&
         (id_ex_pipe_i.alu_operator != ALU_BCLR) && (id_ex_pipe_i.alu_operator != ALU_BSET) &&
         (id_ex_pipe_i.alu_operator != ALU_BREV) && (id_ex_pipe_i.alu_operator != ALU_FF1) &&
         (id_ex_pipe_i.alu_operator != ALU_FL1) && (id_ex_pipe_i.alu_operator != ALU_CNT) &&
         (id_ex_pipe_i.alu_operator != ALU_CLB) && (id_ex_pipe_i.alu_operator != ALU_EXTS) &&
         (id_ex_pipe_i.alu_operator != ALU_EXT) && (id_ex_pipe_i.alu_operator != ALU_LES) &&
         (id_ex_pipe_i.alu_operator != ALU_LEU) && (id_ex_pipe_i.alu_operator != ALU_GTS) &&
         (id_ex_pipe_i.alu_operator != ALU_GTU) && (id_ex_pipe_i.alu_operator != ALU_SLETS) &&
         (id_ex_pipe_i.alu_operator != ALU_SLETU) && (id_ex_pipe_i.alu_operator != ALU_ABS) &&
         (id_ex_pipe_i.alu_operator != ALU_CLIP) && (id_ex_pipe_i.alu_operator != ALU_CLIPU) &&
         (id_ex_pipe_i.alu_operator != ALU_INS) && (id_ex_pipe_i.alu_operator != ALU_MIN) &&
         (id_ex_pipe_i.alu_operator != ALU_MINU) && (id_ex_pipe_i.alu_operator != ALU_MAX) &&
         (id_ex_pipe_i.alu_operator != ALU_MAXU) && (id_ex_pipe_i.alu_operator != ALU_SHUF) &&
         (id_ex_pipe_i.alu_operator != ALU_SHUF2) && (id_ex_pipe_i.alu_operator != ALU_PCKLO) &&
         (id_ex_pipe_i.alu_operator != ALU_PCKHI)));

    


    // Ensure only basic RV32I + DIV*/REM* used
    a_alu_operator_1 : assert property (@(posedge clk) disable iff (!rst_n) (1'b1)
    |-> ((id_ex_pipe_i.alu_operator == ALU_ADD) || (id_ex_pipe_i.alu_operator == ALU_SUB) || (id_ex_pipe_i.alu_operator == ALU_XOR) || (id_ex_pipe_i.alu_operator == ALU_OR) || (id_ex_pipe_i.alu_operator == ALU_AND) ||
         (id_ex_pipe_i.alu_operator == ALU_SRA) || (id_ex_pipe_i.alu_operator == ALU_SRL) || (id_ex_pipe_i.alu_operator == ALU_SLL) || (id_ex_pipe_i.alu_operator == ALU_LTS) || (id_ex_pipe_i.alu_operator == ALU_LTU) ||
         (id_ex_pipe_i.alu_operator == ALU_GES) || (id_ex_pipe_i.alu_operator == ALU_GEU) || (id_ex_pipe_i.alu_operator == ALU_EQ) || (id_ex_pipe_i.alu_operator == ALU_NE) || (id_ex_pipe_i.alu_operator == ALU_SLTS) ||
         (id_ex_pipe_i.alu_operator == ALU_SLTU) || (id_ex_pipe_i.alu_operator == ALU_DIVU) || (id_ex_pipe_i.alu_operator == ALU_DIV) || (id_ex_pipe_i.alu_operator == ALU_REMU) || (id_ex_pipe_i.alu_operator == ALU_REM)));

    // Ensure basic RV32I + DIV*/REM* are encoded such that other operators can be optimized away
    a_alu_operator_2 : assert property (@(posedge clk) disable iff (!rst_n) (1'b1)
    |-> (((id_ex_pipe_i.alu_operator == ALU_ADD) || (id_ex_pipe_i.alu_operator == ALU_SUB) || (id_ex_pipe_i.alu_operator == ALU_XOR) || (id_ex_pipe_i.alu_operator == ALU_OR) || (id_ex_pipe_i.alu_operator == ALU_AND) ||
          (id_ex_pipe_i.alu_operator == ALU_SRA) || (id_ex_pipe_i.alu_operator == ALU_SRL) || (id_ex_pipe_i.alu_operator == ALU_SLL) || (id_ex_pipe_i.alu_operator == ALU_LTS) || (id_ex_pipe_i.alu_operator == ALU_LTU) ||
          (id_ex_pipe_i.alu_operator == ALU_GES) || (id_ex_pipe_i.alu_operator == ALU_GEU) || (id_ex_pipe_i.alu_operator == ALU_EQ) || (id_ex_pipe_i.alu_operator == ALU_NE) || (id_ex_pipe_i.alu_operator == ALU_SLTS) ||
          (id_ex_pipe_i.alu_operator == ALU_SLTU) || (id_ex_pipe_i.alu_operator == ALU_DIVU) || (id_ex_pipe_i.alu_operator == ALU_DIV) || (id_ex_pipe_i.alu_operator == ALU_REMU) || (id_ex_pipe_i.alu_operator == ALU_REM)) == (id_ex_pipe_i.alu_operator[6] == 1'b0)));

`endif

endmodule
