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
// Authors:        Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Description:    RTL assertions for the ex_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_ex_stage_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
#(
  parameter bit X_EXT     = 1'b0
)
(
  input logic           clk,
  input logic           rst_n,

  input logic           ex_ready_o,
  input logic           ex_valid_o,
  input logic           wb_ready_i,
  input logic           wb_valid_i,
  input ctrl_fsm_t      ctrl_fsm_i,

  input id_ex_pipe_t    id_ex_pipe_i,
  input ex_wb_pipe_t    ex_wb_pipe_o,
  input logic           lsu_split_i,
  input logic           csr_illegal_i,

  input logic [31:0]    branch_target_o,
  input logic           branch_taken_ex_ctrl_i,
  input logic           last_op_o
);

  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_ex && !ctrl_fsm_i.kill_ex)
                      |-> (!ex_ready_o && !ex_valid_o))
      else `uvm_error("ex_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_ex)
                      |-> (ex_ready_o && !ex_valid_o))
      else `uvm_error("ex_stage", "Kill should imply ready and not valid")

// Only include following assertions if X_EXT=1
generate
  if(X_EXT == 1'b1) begin
    // csr_en suppressed for xif accepted and pipeline accepted CSR
    // todo:xif Add similar check for rf_we
    a_suppress_csr_xif_legal_pipeline_legal :
    assert property (@(posedge clk) disable iff (!rst_n)
                      ((id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && !csr_illegal_i) &&
                      (id_ex_pipe_i.instr_valid && ex_valid_o && wb_ready_i)
                      |=> !ex_wb_pipe_o.csr_en)
      else `uvm_error("ex_stage", "csr_en not suppressed after eXtension interface and pipeline accepted CSR")

    // csr_en suppressed for xif accepted and pipeline rejected CSR
    // todo:xif Add similar check for rf_we
    a_suppress_csr_xif_legal_pipeline_illegal :
    assert property (@(posedge clk) disable iff (!rst_n)
                      ((id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && csr_illegal_i) &&
                      (id_ex_pipe_i.instr_valid && ex_valid_o && wb_ready_i)
                      |=> !ex_wb_pipe_o.csr_en)
      else `uvm_error("ex_stage", "csr_en not suppressed after eXtension interface accepted and pipeline rejected CSR")
  end
endgenerate

  // csr_en suppressed for xif reject and pipeline reject CSR
  a_suppress_csr_xif_illegal_pipeline_illegal :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (!(id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && csr_illegal_i) &&
                    (id_ex_pipe_i.instr_valid && ex_valid_o && wb_ready_i)
                    |=> !ex_wb_pipe_o.csr_en && !ex_wb_pipe_o.rf_we)
    else `uvm_error("ex_stage", "csr_en or rf_we not suppressed after eXtension interface rejected and pipeline rejected CSR")

  // csr_en not suppressed for xif reject and pipeline accept CSR
  a_suppress_csr_xif_illegal_pipeline_legal :
  assert property (@(posedge clk) disable iff (!rst_n)
                    (!(id_ex_pipe_i.xif_en && id_ex_pipe_i.xif_meta.accepted) && id_ex_pipe_i.csr_en && !csr_illegal_i) &&
                    (id_ex_pipe_i.instr_valid && ex_valid_o && wb_ready_i)
                    |=> ex_wb_pipe_o.csr_en && ex_wb_pipe_o.rf_we)
    else `uvm_error("ex_stage", "csr_en or rf_we suppressed after eXtension interface rejected and pipeline accepted CSR")

  // First access of split LSU instruction should have rf_we deasserted
  a_split_rf_we:
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ex_valid_o && wb_ready_i && id_ex_pipe_i.lsu_en && lsu_split_i)
                      |=> !ex_wb_pipe_o.rf_we);

  // Ensure that functional unit enables are one-hot (ALU and DIV both use the ALU though)
  a_functional_unit_enable_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot0({id_ex_pipe_i.alu_en, id_ex_pipe_i.div_en, id_ex_pipe_i.mul_en,
                     id_ex_pipe_i.csr_en, id_ex_pipe_i.sys_en, id_ex_pipe_i.lsu_en, id_ex_pipe_i.xif_en}))
      else `uvm_error("ex_stage", "Multiple functional units enabled")

  // Check that branch target remains constant while a branch instruction is in EX
  // Branches are taken during their first un-stalled cycle in EX. If the target changes before
  // the branch can move to WB, we might have taken the branch before an unresolved dependency.
  property p_bch_target_stable;
    logic [31:0] bch_target;
    @(posedge clk) disable iff (!rst_n)
    (branch_taken_ex_ctrl_i, bch_target=branch_target_o)
    |->
    (bch_target == branch_target_o) until_with ((ex_valid_o && wb_ready_i && last_op_o) || ctrl_fsm_i.kill_ex);
  endproperty

  a_bch_target_stable: assert property (p_bch_target_stable)
    else `uvm_error("ex_stage", "Branch target not stable")

  // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
  // and that EX stage is ready to receive flushed instruction immediately, as long as there's no backpressure from WB
  property p_branch_taken_ex_flush;
    @(posedge clk) disable iff (!rst_n)
      ((branch_taken_ex_ctrl_i == 1'b1) && !(ctrl_fsm_i.kill_ex || ctrl_fsm_i.halt_ex ) && wb_ready_i |->
       ex_ready_o ##1 (id_ex_pipe_i.instr_valid == 1'b0));
  endproperty : p_branch_taken_ex_flush

  a_branch_taken_ex_flush : assert property(p_branch_taken_ex_flush)
    else `uvm_error("id_stage", "Assertion p_branch_taken_ex failed")

  // Check that there's a bubble in EX when there's a taken branch in WB
  // This complements a_branch_taken_ex_flush as a_branch_taken_ex_flush wil not check anything if there's backpressure from WB
  // when a branch is taken
  property p_bubble_ex_when_branch_taken_wb;
    @(posedge clk) disable iff (!rst_n)
      ( ex_wb_pipe_o.alu_bch_taken_qual && wb_valid_i|->
        (id_ex_pipe_i.instr_valid == 1'b0));
  endproperty : p_bubble_ex_when_branch_taken_wb

  a_bubble_ex_when_branch_taken_wb : assert property(p_bubble_ex_when_branch_taken_wb)
    else `uvm_error("id_stage", "Assertion p_branch_taken_ex failed")

endmodule // cv32e40x_ex_stage_sva
