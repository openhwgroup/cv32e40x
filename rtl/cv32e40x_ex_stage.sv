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
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
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

  input  logic        halt_ex_i,
  input  logic        kill_ex_i,
  // ID/EX pipeline
  input id_ex_pipe_t  id_ex_pipe_i,

  // CSR access
  input  logic [31:0] csr_rdata_i,

  // EX/WB pipeline 
  output ex_wb_pipe_t ex_wb_pipe_o,

  // Register file forwarding signals (to ID)
  output logic        rf_we_ex_o,
  output rf_addr_t    rf_waddr_ex_o,
  output logic [31:0] rf_wdata_ex_o,

  // To IF: Jump and branch target and decision
  output logic        branch_decision_o,
  output logic [31:0] branch_target_o,

  // Stall Control
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

  // Local signals after evaluating with instr_valid
  logic alu_en_gated;
  logic mult_en_gated;
  logic csr_en_gated;
  logic rf_we_gated;
  
  assign alu_en_gated = id_ex_pipe_i.alu_en && id_ex_pipe_i.instr_valid && !kill_ex_i;
  assign mult_en_gated = id_ex_pipe_i.mult_en && id_ex_pipe_i.instr_valid && !kill_ex_i;
  assign csr_en_gated = id_ex_pipe_i.csr_en && id_ex_pipe_i.instr_valid && !kill_ex_i;
  assign rf_we_gated = id_ex_pipe_i.rf_we && id_ex_pipe_i.instr_valid && !kill_ex_i;

  // ALU write port mux
  always_comb
  begin
    rf_wdata_ex_o = 'b0; // TODO:OK get rid of this and make alu/mult/csr_en unique

    rf_we_ex_o    = rf_we_gated;
    rf_waddr_ex_o = id_ex_pipe_i.rf_waddr;
    if (alu_en_gated)
      rf_wdata_ex_o = alu_result;
    if (mult_en_gated)
      rf_wdata_ex_o = mult_result;
    if (csr_en_gated)
      rf_wdata_ex_o = csr_rdata_i;
  end

  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign branch_target_o   = id_ex_pipe_i.operand_c;

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
    .enable_i            ( alu_en_gated               ),
    .operator_i          ( id_ex_pipe_i.alu_operator  ),
    .operand_a_i         ( id_ex_pipe_i.alu_operand_a ),
    .operand_b_i         ( id_ex_pipe_i.alu_operand_b ),

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

    .kill_i          ( kill_ex_i                     ),
    .enable_i        ( mult_en_gated                 ),
    .operator_i      ( id_ex_pipe_i.mult_operator    ),

    .short_signed_i  ( id_ex_pipe_i.mult_signed_mode ),

    .op_a_i          ( id_ex_pipe_i.mult_operand_a   ),
    .op_b_i          ( id_ex_pipe_i.mult_operand_b   ),

    .result_o        ( mult_result                   ),

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
      ex_wb_pipe_o.instr_valid    <= 1'b0;
      ex_wb_pipe_o.rf_we          <= 1'b0;
      ex_wb_pipe_o.rf_waddr       <= '0;
      ex_wb_pipe_o.rf_wdata       <= 32'b0;
      ex_wb_pipe_o.data_req       <= 1'b0;

      ex_wb_pipe_o.pc             <= 32'h0;
      ex_wb_pipe_o.instr          <= INST_RESP_RESET_VAL;
      ex_wb_pipe_o.illegal_insn   <= 1'b0;
      ex_wb_pipe_o.ebrk_insn      <= 1'b0;
      ex_wb_pipe_o.wfi_insn       <= 1'b0;
      ex_wb_pipe_o.ecall_insn     <= 1'b0;
      ex_wb_pipe_o.fencei_insn    <= 1'b0;
      ex_wb_pipe_o.mret_insn      <= 1'b0;
      ex_wb_pipe_o.dret_insn      <= 1'b0;
      ex_wb_pipe_o.data_mpu_status <= MPU_OK;

      ex_wb_pipe_o.csr_en         <= 1'b0;
      ex_wb_pipe_o.csr_access     <= 1'b0;
      ex_wb_pipe_o.csr_op         <= CSR_OP_READ;
      ex_wb_pipe_o.csr_addr       <= '0;
      ex_wb_pipe_o.csr_wdata      <= 32'h00000000;
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i and id_ex_pipe_i.instr_valid is implied
      begin
        ex_wb_pipe_o.instr_valid <= 1'b1;
        ex_wb_pipe_o.rf_we <= id_ex_pipe_i.rf_we;
        ex_wb_pipe_o.data_req <= id_ex_pipe_i.data_req;
          
        if (id_ex_pipe_i.rf_we) begin
          ex_wb_pipe_o.rf_waddr <= id_ex_pipe_i.rf_waddr;
          if (!id_ex_pipe_i.data_req) begin
            ex_wb_pipe_o.rf_wdata <= rf_wdata_ex_o;
          end
        end

        // Update signals for CSR access in WB
        ex_wb_pipe_o.csr_en  <= id_ex_pipe_i.csr_en;
        ex_wb_pipe_o.csr_access <= id_ex_pipe_i.csr_access; // TODO:OK: May revert to using only csr_en with the new instr_valid qualifier?
        ex_wb_pipe_o.csr_op <= id_ex_pipe_i.csr_op;
        if (id_ex_pipe_i.csr_en) begin
          ex_wb_pipe_o.csr_addr <= id_ex_pipe_i.alu_operand_b[11:0];
          ex_wb_pipe_o.csr_wdata <= id_ex_pipe_i.alu_operand_a;
        end

        // Propagate signals needed for exception handling in WB
        // TODO:OK: Clock gating of pc if no existing exceptions
        //          and LSU it not in use
        ex_wb_pipe_o.pc                     <= id_ex_pipe_i.pc;
        ex_wb_pipe_o.instr                  <= id_ex_pipe_i.instr;
        ex_wb_pipe_o.illegal_insn           <= id_ex_pipe_i.illegal_insn;
        ex_wb_pipe_o.ebrk_insn              <= id_ex_pipe_i.ebrk_insn;
        ex_wb_pipe_o.wfi_insn               <= id_ex_pipe_i.wfi_insn;
        ex_wb_pipe_o.ecall_insn             <= id_ex_pipe_i.ecall_insn;
        ex_wb_pipe_o.fencei_insn            <= id_ex_pipe_i.fencei_insn;
        ex_wb_pipe_o.mret_insn              <= id_ex_pipe_i.mret_insn;
        ex_wb_pipe_o.dret_insn              <= id_ex_pipe_i.dret_insn;
        ex_wb_pipe_o.data_mpu_status        <= MPU_OK; // TODO:OK: Set to actual MPU status when MPU is implemented on data side.
        ex_wb_pipe_o.trigger_match          <= id_ex_pipe_i.trigger_match;
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        ex_wb_pipe_o.instr_valid <= 1'b0;
        //ex_wb_pipe_o.rf_we <= 1'b0;
      end
    end
  end

  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.
  assign ex_ready_o = (alu_ready && mult_ready && lsu_ready_ex_i
                       && wb_ready_i && !halt_ex_i);// || (id_ex_pipe_i.branch_in_ex && id_ex_pipe_i.instr_valid);// TODO: This done to support a simplification for RVFI and has not been verified
  assign ex_valid_o = (alu_ready && mult_ready && lsu_ready_ex_i && wb_ready_i) && id_ex_pipe_i.instr_valid && !kill_ex_i;

endmodule // cv32e40x_ex_stage
