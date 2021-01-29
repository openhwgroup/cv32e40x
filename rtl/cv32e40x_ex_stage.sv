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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MULT: computes normal multiplications                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_ex_stage import cv32e40x_pkg::*;
(
  input  logic        clk,
  input  logic        rst_n,

  // ID/EX pipeline
  input id_ex_pipe_t  id_ex_pipe_i,

  output logic        mult_multicycle_o,

  input  logic [31:0] lsu_rdata_i,

  // CSR access
  input  logic [31:0] csr_rdata_i,

  // EX/WB pipeline 
  output ex_wb_pipe_t ex_wb_pipe_o,

  // Register file forwarding signals (to ID)
  output logic        rf_we_ex_o,
  output rf_addr_t    rf_waddr_ex_o,
  output logic [31:0] rf_wdata_ex_o,

  // To IF: Jump and branch target and decision
  output logic [31:0] jump_target_o,
  output logic        branch_decision_o,

  // Stall Control
  input logic         is_decoding_i, // Used to mask data Dependency inside the APU dispatcher in case of an istruction non valid
  input logic         lsu_ready_ex_i, // EX part of LSU is done

  output logic        ex_ready_o, // EX stage ready for new data
  output logic        ex_valid_o, // EX stage gets new data
  input  logic        wb_ready_i  // WB stage ready for new data
);

  logic [31:0]    alu_result;
  logic [31:0]    mult_result;
  logic           alu_cmp_result;

  logic           alu_ready;
  logic           mult_ready;

  // ALU write port mux
  always_comb
  begin
    rf_wdata_ex_o = '0; // todo: assignments below should be unique case (also check with formal if assignment to 0 is needed, and if so comment why)

    rf_we_ex_o    = id_ex_pipe_i.rf_we;
    rf_waddr_ex_o = id_ex_pipe_i.rf_waddr;
    if (id_ex_pipe_i.alu_en)
      rf_wdata_ex_o = alu_result;
    if (id_ex_pipe_i.mult_en)
      rf_wdata_ex_o = mult_result;
    if (id_ex_pipe_i.csr_access)
      rf_wdata_ex_o = csr_rdata_i;
  end

  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign jump_target_o     = id_ex_pipe_i.alu_operand_c;


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  cv32e40x_alu alu_i
  (
    .clk                 ( clk                        ),
    .rst_n               ( rst_n                      ),
    .enable_i            ( id_ex_pipe_i.alu_en        ),
    .operator_i          ( id_ex_pipe_i.alu_operator  ),
    .operand_a_i         ( id_ex_pipe_i.alu_operand_a ),
    .operand_b_i         ( id_ex_pipe_i.alu_operand_b ),
    .operand_c_i         ( id_ex_pipe_i.alu_operand_c ),

    .result_o            ( alu_result                 ),
    .comparison_result_o ( alu_cmp_result             ),

    .ready_o             ( alu_ready                  ),
    .ex_ready_i          ( ex_ready_o                 )
  );


  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  cv32e40x_mult mult_i
  (
    .clk             ( clk                           ),
    .rst_n           ( rst_n                         ),

    .enable_i        ( id_ex_pipe_i.mult_en          ),
    .operator_i      ( id_ex_pipe_i.mult_operator    ),

    .short_subword_i ( id_ex_pipe_i.mult_sel_subword ),
    .short_signed_i  ( id_ex_pipe_i.mult_signed_mode ),

    .op_a_i          ( id_ex_pipe_i.mult_operand_a   ),
    .op_b_i          ( id_ex_pipe_i.mult_operand_b   ),
    .op_c_i          ( id_ex_pipe_i.mult_operand_c   ),

    .result_o        ( mult_result                   ),
					             
    .multicycle_o    ( mult_multicycle_o             ),
    .ready_o         ( mult_ready                    ),
    .ex_ready_i      ( ex_ready_o                    )
  );

  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_PIPE_REGISTERS
    if (~rst_n)
    begin
      ex_wb_pipe_o.rf_we    <= 1'b0;
      ex_wb_pipe_o.rf_waddr <= '0;
      ex_wb_pipe_o.rf_wdata <= 32'b0; // todo: regular assignment needs to be added while removing 2nd rf write port
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        ex_wb_pipe_o.rf_we <= id_ex_pipe_i.rf_we && id_ex_pipe_i.data_req;
        if (id_ex_pipe_i.rf_we && id_ex_pipe_i.data_req) begin
          ex_wb_pipe_o.rf_waddr <= id_ex_pipe_i.rf_waddr;
        end
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        ex_wb_pipe_o.rf_we <= 1'b0;
      end
    end
  end

  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.
  assign ex_ready_o = (alu_ready && mult_ready && lsu_ready_ex_i
                       && wb_ready_i) || (id_ex_pipe_i.branch_in_ex);
  assign ex_valid_o = (id_ex_pipe_i.alu_en || id_ex_pipe_i.mult_en || id_ex_pipe_i.csr_access || id_ex_pipe_i.data_req)
                       && (alu_ready && mult_ready && lsu_ready_ex_i && wb_ready_i);

endmodule // cv32e40x_ex_stage
