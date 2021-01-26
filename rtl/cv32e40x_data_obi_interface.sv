// Copyright 2020 Silicon Labs, Inc.
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
// Design Name:    OBI (Open Bus Interface)                                   //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Open Bus Interface adapter. Translates transaction request //
//                 on the trans_* interface into an OBI A channel transfer.   //
//                 The OBI R channel transfer translated (i.e. passed on) as  //
//                 a transaction response on the resp_* interface.            //
//                                                                            //
//                 This adapter does not limit the number of outstanding      //
//                 OBI transactions in any way.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_data_obi_interface import cv32e40x_pkg::*;
(
  input  logic        clk,
  input  logic        rst_n,

  // Transaction request interface
  input  logic        trans_valid_i,
  output logic        trans_ready_o,
  input  logic [31:0] trans_addr_i,
  input  logic        trans_we_i,
  input  logic  [3:0] trans_be_i,
  input  logic [31:0] trans_wdata_i,
  input  logic  [5:0] trans_atop_i,             // Future proof addition (not part of OBI 1.0 spec; not used in CV32E40P)

  // Transaction response interface
  output logic        resp_valid_o,             // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
  output logic [31:0] resp_rdata_o,
  output logic        resp_err_o,

  // OBI interface
  if_obi_data.master obi_bus

);

  obi_if_state_e state_q, next_state;

  //////////////////////////////////////////////////////////////////////////////
  // OBI R Channel
  //////////////////////////////////////////////////////////////////////////////

  // The OBI R channel signals are passed on directly on the transaction response
  // interface (resp_*). It is assumed that the consumer of the transaction response
  // is always receptive when resp_valid_o = 1 (otherwise a response would get dropped)

  assign resp_valid_o = obi_bus.rvalid;
  assign resp_rdata_o = obi_bus.r_payload.rdata;
  assign resp_err_o   = obi_bus.r_payload.err;


  //////////////////////////////////////////////////////////////////////////////
  // OBI A Channel
  //////////////////////////////////////////////////////////////////////////////


  // If the incoming transaction itself is stable, then it satisfies the OBI protocol
  // and signals can be passed to/from OBI directly.
  assign obi_bus.req               = trans_valid_i;
  assign obi_bus.a_payload.addr    = trans_addr_i;
  assign obi_bus.a_payload.we      = trans_we_i;
  assign obi_bus.a_payload.be      = trans_be_i;
  assign obi_bus.a_payload.wdata   = trans_wdata_i;
  assign obi_bus.a_payload.atop    = trans_atop_i;

  assign trans_ready_o = obi_bus.gnt;


  

endmodule // cv32e40x_obi_interface
