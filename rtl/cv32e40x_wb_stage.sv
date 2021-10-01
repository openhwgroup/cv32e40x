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

  // LSU
  input  logic [31:0]   lsu_rdata_i,
  input  mpu_status_e   lsu_mpu_status_i,

  // Register file interface
  output logic          rf_we_wb_o,     // Register file write enable
  output rf_addr_t      rf_waddr_wb_o,  // Register file write address
  output logic [31:0]   rf_wdata_wb_o,  // Register file write data

  // LSU handshake interface
  input  logic          lsu_valid_i,
  output logic          lsu_ready_o,
  output logic          lsu_valid_o,
  input  logic          lsu_ready_i,

  // WB stalled by LSU
  output logic          data_stall_o,

  // Stage ready/valid
  output logic          wb_ready_o,
  output logic          wb_valid_o
);

  logic                 instr_valid;
  logic                 wb_valid;
  logic                 lsu_exception;

  assign instr_valid = ex_wb_pipe_i.instr_valid && !ctrl_fsm_i.kill_wb && !ctrl_fsm_i.halt_wb;

  assign lsu_exception = (lsu_mpu_status_i != MPU_OK);

  //////////////////////////////////////////////////////////////////////////////
  // Controller interface todo: move/remove this block of comment?
  //
  // LSU enabled computed as in EX stage, however once a load/store transaction
  // is this far in the pipeline it should not longer get killed (as its
  // data_req_o/data_ack_i handshake has already occurred. This is checked
  // with the a_lsu_no_kill assertion.



  //////////////////////////////////////////////////////////////////////////////
  // Register file interface
  //
  // Note that write back is not suppressed during bus errors (in order to prevent
  // a timing path from the late arriving data_err_i into the register file).
  //
  // Note that the register file is only written for the last part of a split misaligned load.
  // (rf_we suppressed in ex_stage for the first part, lsu aggregates data for second part)
  //
  // Note that the register file is written multiple times in case waited loads (in
  // order to prevent a timing path from the late arriving data_rvalid_i into the
  // register file.
  //
  // In case of MPU/PMA error, the register file should not be written.
  // rf_we_wb_o is deasserted if lsu_mpu_status is not equal to MPU_OK

  assign rf_we_wb_o     = ex_wb_pipe_i.rf_we && !lsu_exception && instr_valid;
  assign rf_waddr_wb_o  = ex_wb_pipe_i.rf_waddr;
  assign rf_wdata_wb_o  = ex_wb_pipe_i.lsu_en ? lsu_rdata_i : ex_wb_pipe_i.rf_wdata;

  //////////////////////////////////////////////////////////////////////////////
  // LSU inputs are valid when LSU is enabled; LSU outputs need to remain valid until downstream stage is ready

  // Does not depend on local instr_valid (ie kept high for stalls and kills)
  // Ok, as controller will never kill ongoing LSU instructions, and thus
  // the lsu valid_1_o which lsu_valid_o factors into should not be affected.
  assign lsu_valid_o = ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid; // todo: move to LSU?
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
  // - Will be 1 only for the second phase of a split misaligned load/store that completes without MPU errors.
  //   If an MPU error occurs, wb_valid will be 1 due to lsu_exception (for any phase where the error occurs)

  assign wb_valid = ((!ex_wb_pipe_i.lsu_en && 1'b1)        ||     // Non-LSU instructions always have valid result in WB, also for exceptions.
                     ( ex_wb_pipe_i.lsu_en && lsu_valid_i) ||     // LSU instructions have valid result based on data_rvalid_i
                     ( ex_wb_pipe_i.lsu_en && lsu_exception)      // LSU instruction had an exception
                    ) && instr_valid;

  assign wb_valid_o = wb_valid;

  // Export signal indicating WB stage stalled by load/store
  assign data_stall_o = (ex_wb_pipe_i.lsu_en && !lsu_valid_i) && instr_valid;
  
endmodule // cv32e40x_wb_stage
