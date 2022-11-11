// Copyright 2022 Silicon Labs, Inc.
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
// Engineer:       Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Debug triggers                                             //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Module containing 0-4 triggers for debug                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_debug_triggers
import cv32e40x_pkg::*;
#(
  parameter int DBG_NUM_TRIGGERS = 1
)
(
  input  logic       clk,
  input  logic       rst_n,

  // CSR inputs write inputs
  input  logic [31:0] csr_wdata_i,
  input  logic        tselect_we_i,
  input  logic        tdata1_we_i,
  input  logic        tdata2_we_i,
  input  logic        tdata3_we_i,
  input  logic        tinfo_we_i,
  input  logic        tcontrol_we_i,

  // CSR read data outputs
  output logic [31:0] tselect_rdata_o,
  output logic [31:0] tdata1_rdata_o,
  output logic [31:0] tdata2_rdata_o,
  output logic [31:0] tdata3_rdata_o,
  output logic [31:0] tinfo_rdata_o,
  output logic [31:0] tcontrol_rdata_o,

  // IF stage inputs
  input  logic [31:0] pc_if_i,
  input  logic        ptr_in_if_i,

  // Controller inputs
  input ctrl_fsm_t    ctrl_fsm_i,

  // Trigger match output
  output logic        trigger_match_o
);

  // CSR write data
  logic [31:0] tselect_n;
  logic [31:0] tdata1_n;
  logic [31:0] tdata2_n;
  logic [31:0] tdata3_n;
  logic [31:0] tinfo_n;
  logic [31:0] tcontrol_n;

  // CSR instance outputs
  logic [31:0] tdata1_q;
  logic [31:0] tdata2_q;

  logic unused_signals;

  // Write data
  always_comb begin
    tselect_n     = tselect_rdata_o; // todo

    tdata1_n      = {
                     TTYPE_MCONTROL,        // type    : address/data match
                     1'b1,                  // dmode   : access from D mode only
                     6'h00,                 // maskmax : exact match only
                     1'b0,                  // hit     : not supported
                     1'b0,                  // select  : address match only
                     1'b0,                  // timing  : match before execution
                     2'b00,                 // sizelo  : match any access
                     4'h1,                  // action  : enter debug mode
                     1'b0,                  // chain   : not supported
                     4'h0,                  // match   : simple match
                     1'b1,                  // m       : match in m-mode
                     1'b0,                  // 0       : zero
                     1'b0,                  // s       : not supported
                     1'b0,                  // u       : match in u-mode
                     csr_wdata_i[2],        // execute : match instruction address
                     1'b0,                  // store   : not supported
                     1'b0                   // load    : not supported
                     };

    tdata2_n      = csr_wdata_i;
    tdata3_n      = tdata3_rdata_o;   // Read only
    tinfo_n       = tinfo_rdata_o;    // Read only
    tcontrol_n    = tcontrol_rdata_o; // Read only
  end

  // Breakpoint matching
  // We match against the next address, as the breakpoint must be taken before execution
  // Matching is disabled when ctrl_fsm_i.debug_mode == 1'b1
  // Trigger CSRs can only be written from debug mode, writes from any other privilege level are ignored.
  //   Thus we do not have an issue where a write to the tdata2 CSR immediately before the matched instruction
  //   could be missed since we must write in debug mode, then dret to machine mode (kills pipeline) before
  //   returning to dpc.
  //   Todo: There is no CLIC spec for trigger matches for pointers.
  assign trigger_match_o = tdata1_rdata_o[2] && !ctrl_fsm_i.debug_mode && !ptr_in_if_i &&
                          (pc_if_i[31:0] == tdata2_rdata_o[31:0]);


  cv32e40x_csr
  #(
    .WIDTH      (32),
    .RESETVALUE (TDATA1_RST_VAL)
  )
  tdata1_csr_i
  (
    .clk                ( clk                   ),
    .rst_n              ( rst_n                 ),
    .wr_data_i          ( tdata1_n              ),
    .wr_en_i            ( tdata1_we_i           ),
    .rd_data_o          ( tdata1_q              )
  );

  cv32e40x_csr
  #(
    .WIDTH      (32),
    .RESETVALUE (32'd0)
  )
  tdata2_csr_i
  (
    .clk                ( clk                   ),
    .rst_n              ( rst_n                 ),
    .wr_data_i          ( tdata2_n              ),
    .wr_en_i            ( tdata2_we_i           ),
    .rd_data_o          ( tdata2_q              )
  );

  // Assign CSR read data outputs
  assign tdata1_rdata_o   = tdata1_q;
  assign tdata2_rdata_o   = tdata2_q;
  assign tdata3_rdata_o   = 32'h00000000;
  assign tselect_rdata_o  = 32'h00000000;
  assign tinfo_rdata_o    = 32'h4;
  assign tcontrol_rdata_o = 32'h00000000;

  assign unused_signals = tselect_we_i | tinfo_we_i | tcontrol_we_i | tdata3_we_i;
endmodule
