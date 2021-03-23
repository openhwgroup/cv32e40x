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

  input  logic [31:0]   lsu_rdata_i,

  output logic          rf_we_wb_o,
  output rf_addr_t      rf_waddr_wb_o,
  output logic [31:0]   rf_wdata_wb_o,

  // to JR forward logic
  output logic          wb_alu_en_o
);

  assign rf_we_wb_o    = ex_wb_pipe_i.rf_we;
  assign rf_waddr_wb_o = ex_wb_pipe_i.rf_waddr;
  assign rf_wdata_wb_o = ex_wb_pipe_i.rf_wdata_ex_en ? ex_wb_pipe_i.rf_wdata : lsu_rdata_i;
  assign wb_alu_en_o   = ex_wb_pipe_i.rf_wdata_ex_en;

endmodule // cv32e40x_wb_stage
