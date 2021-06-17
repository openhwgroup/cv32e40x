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
  // EX/WB pipeline 
  input  ex_wb_pipe_t   ex_wb_pipe_i,

  // From controller FSM
  input  ctrl_fsm_t     ctrl_fsm_i,

  input  logic [31:0]   lsu_rdata_i,
  input  logic [31:0]   csr_rdata_i,
  input  logic          lsu_ready_wb_i,

  output logic          rf_we_wb_o,
  output rf_addr_t      rf_waddr_wb_o,
  output logic [31:0]   rf_wdata_wb_o,

  output logic          wb_valid_o,

  // to JR forward logic
  output logic          data_req_wb_o

);

logic  instr_valid;
assign instr_valid = ex_wb_pipe_i.instr_valid && !ctrl_fsm_i.kill_wb;

// We allow writebacks in case of bus errors.
// Otherwise we would get a timing path from rvalid to rf_we

// Regfile is also written multiple times in case of misaligned
// load/stores that require two transactions.

  assign rf_we_wb_o    = ex_wb_pipe_i.rf_we && instr_valid && !ctrl_fsm_i.halt_wb; // TODO:OK: deassert in case of MPU error
  assign rf_waddr_wb_o = ex_wb_pipe_i.rf_waddr;

  assign rf_wdata_wb_o = ex_wb_pipe_i.data_req ? lsu_rdata_i : ex_wb_pipe_i.rf_wdata;

  assign data_req_wb_o = ex_wb_pipe_i.data_req && instr_valid;

  assign wb_valid_o    = lsu_ready_wb_i && !ctrl_fsm_i.halt_wb && instr_valid;
  
endmodule // cv32e40x_wb_stage
