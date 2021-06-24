// Copyright 2021 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Write Back stage                                           //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Write back stage: Hosts write back from load/store unit    //
//                 and combined write back from ALU/MULT/DIV/CSR.             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_wb_stage import cv32e40x_pkg::*;
(
  input  logic          clk,            // Not used in RTL; only used by assertions
  input  logic          rst_n,          // Not used in RTL; only used by assertions

  // EX/WB pipeline 
  input  ex_wb_pipe_t   ex_wb_pipe_i,

  // Controller
  input  ctrl_fsm_t     ctrl_fsm_i,
  output logic          lsu_en_wb_o,    // Used in forward/stall logic

  // LSU
  input  logic [31:0]   lsu_rdata_i,

  // Register file interface
  output logic          rf_we_wb_o,     // Register file write enable
  output rf_addr_t      rf_waddr_wb_o,  // Register file write address
  output logic [31:0]   rf_wdata_wb_o,  // Register file write data

  // LSU handshake interface
  input  logic          lsu_valid_i,
  output logic          lsu_ready_o,
  output logic          lsu_valid_o,
  input  logic          lsu_ready_i,

  // Stage ready/valid
  output logic          wb_ready_o
);

  logic                 instr_valid;
  logic                 wb_valid;       // Only used by RVFI
  logic                 lsu_en_gated;   // LSU enabled gated with all disqualifiers

  assign instr_valid = ex_wb_pipe_i.instr_valid && !ctrl_fsm_i.kill_wb && !ctrl_fsm_i.halt_wb;

  //////////////////////////////////////////////////////////////////////////////
  // Controller interface
  //
  // LSU enabled computed as in EX stage, however once a load/store transaction
  // is this far in the pipeline it should not longer get killed (as its
  // data_req_o/data_ack_i handshake has already occurred. This is checked
  // with the a_lsu_no_kill assertion.

  assign lsu_en_gated = ex_wb_pipe_i.lsu_en && instr_valid;
  assign lsu_en_wb_o  = lsu_en_gated;

  //////////////////////////////////////////////////////////////////////////////
  // Register file interface
  //
  // Note that write back is not suppressed during bus errors (in order to prevent
  // a timing path from the late arriving data_err_i into the register file).
  //
  // Note that the register file is written twice in case of a misaligned load.
  //
  // Note that the register file is written multiple times in case waited loads (in
  // order to prevent a timing path from the late arriving data_rvalid_i into the
  // register file.

  assign rf_we_wb_o    = ex_wb_pipe_i.rf_we && instr_valid ; // TODO:OK:low deassert in case of MPU error (already do this in EX stage)
  assign rf_waddr_wb_o = ex_wb_pipe_i.rf_waddr;
  assign rf_wdata_wb_o = ex_wb_pipe_i.lsu_en ? lsu_rdata_i : ex_wb_pipe_i.rf_wdata;

  //////////////////////////////////////////////////////////////////////////////
  // LSU inputs are valid when LSU is enabled; LSU outputs need to remain valid until downstream stage is ready

  assign lsu_valid_o = lsu_en_gated;
  assign lsu_ready_o = 1'b1; // Always ready (there is no downstream stage)

  //////////////////////////////////////////////////////////////////////////////
  // Stage ready/valid

  assign wb_ready_o = lsu_ready_i;

  // todo: Above hould have similar structure as ex_ready_o
  // todo: Want the following expression, but currently not SEC clean; might just be caused by fact that OBI assumes are not loaded during SEC
  //  assign wb_ready_o = ctrl_fsm_i.kill_wb || (lsu_ready_i && !ctrl_fsm_i.halt_wb);

  // wb_valid
  //
  // - Will be 0 for interrupted instruction and debug entry
  // - Will be 1 for synchronous exceptions (which is easier to deal with for RVFI); this implies that wb_valid
  //   cannot be used to increment the minstret CSR (as that should not increment for e.g. ecall, ebreak, etc.)
  // - Will be 1 only for the second phase of a misaligned load/store

  assign wb_valid = ((!ex_wb_pipe_i.lsu_en && 1'b1) ||          // Non-LSU instructions always have valid result in WB
                     ( ex_wb_pipe_i.lsu_en && lsu_valid_i)      // LSU instructions have valid result based on data_rvalid_i
                    ) && instr_valid;
  
endmodule // cv32e40x_wb_stage
