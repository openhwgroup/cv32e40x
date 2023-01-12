// Copyright 2023 Silicon Labs, Inc.
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
// Authors:        Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    debug_triggers assertions                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_debug_triggers_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
#(
    parameter int DBG_NUM_TRIGGERS = 1
  )

  (
   input logic        clk,
   input logic        rst_n,
   input csr_opcode_e csr_op,       // from cs_registers
   input logic [31:0] csr_wdata,    // from cs_registers
   input csr_num_e    csr_waddr,    // from cs_registers
   input ex_wb_pipe_t ex_wb_pipe_i,
   input ctrl_fsm_t   ctrl_fsm_i,
   input logic [31:0] tselect_q,
   input logic [31:0] tdata1_q[DBG_NUM_TRIGGERS],
   input logic [31:0] tdata2_q[DBG_NUM_TRIGGERS]
  );



  /////////////////////////////////////////////////////////////////////////////////////////
  // Asserts to check that the CSR flops remain unchanged if a set/clear has all_zero rs1
  /////////////////////////////////////////////////////////////////////////////////////////
  a_set_clear_tselect_q:
  assert property (@(posedge clk) disable iff (!rst_n)
                  (csr_waddr == CSR_TSELECT) &&
                  ((csr_op == CSR_OP_SET) || (csr_op == CSR_OP_CLEAR)) &&
                  !(|csr_wdata) &&
                  ex_wb_pipe_i.csr_en &&
                  !ctrl_fsm_i.kill_wb
                  |=>
                  $stable(tselect_q))
    else `uvm_error("debug_triggers", "tselect_q changed after set/clear with rs1==0")

  a_set_clear_tdata1_q:
  assert property (@(posedge clk) disable iff (!rst_n)
                  (csr_waddr == CSR_TDATA1) &&
                  ((csr_op == CSR_OP_SET) || (csr_op == CSR_OP_CLEAR)) &&
                  !(|csr_wdata) &&
                  ex_wb_pipe_i.csr_en &&
                  !ctrl_fsm_i.kill_wb
                  |=>
                  $stable(tdata1_q)) // Checking stability of ALL tdata1, not just the one selected
    else `uvm_error("debug_triggers", "tdata1_q changed after set/clear with rs1==0")

  a_set_clear_tdata2_q:
  assert property (@(posedge clk) disable iff (!rst_n)
                  (csr_waddr == CSR_TDATA2) &&
                  ((csr_op == CSR_OP_SET) || (csr_op == CSR_OP_CLEAR)) &&
                  !(|csr_wdata) &&
                  ex_wb_pipe_i.csr_en &&
                  !ctrl_fsm_i.kill_wb
                  |=>
                  $stable(tdata2_q)) // Checking stability of ALL tdata2, not just the one selected
    else `uvm_error("debug_triggers", "tdata2_q changed after set/clear with rs1==0")


endmodule

