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
// Engineer:       Halfdan Bechmann  -  halfdan.bechmann@silabs.com           //
//                                                                            //
// Design Name:    Write Buffer                                               //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Response filter for the LSU. Used to return rvalid early   //
//                 for bufferable transfers.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_lsu_response_filter
  import cv32e40x_pkg::*;
  (
   // clock and reset
   input logic           clk,
   input logic           rst_n,

   // inputs
   input  logic          valid_i,
   input  obi_data_req_t trans_i,
   input  logic          ready_i,

   input  logic          resp_valid_i,

   // outputs
   output logic          valid_o,
   output obi_data_req_t trans_o,
   output logic          ready_o,

   output logic          busy_o,
   output logic          resp_valid_o
   );
  localparam DEPTH     = 2;
  localparam CNT_WIDTH = $clog2(DEPTH+1);

  logic [CNT_WIDTH-1:0]  cnt_q;
  logic [CNT_WIDTH-1:0]  next_cnt;
  logic                  count_up;
  logic                  count_down;

  logic                  trans_accepted;

  logic                  bufferable_resp; // Bufferable transfer response
  logic                  bufferable_resp_q;
  logic                  non_bufferable_pending;
  logic                  resp_is_bufferable;

  // Shift register containing bufferable cofiguration of outstanding transfers
  logic [DEPTH:0]        outstanding_bufferable_q;
  logic [DEPTH:0]        outstanding_bufferable_next;

  assign busy_o             = (cnt_q != '0) || valid_i;

  assign trans_accepted     = ready_i && valid_o; // Transfer accepted on the bus side of the response filter

  assign resp_is_bufferable = outstanding_bufferable_q[cnt_q]; // Bufferable configuration of the oldest outstanding transfer

  // A bufferable transfer will generally issue a valid response in the the next cycle. However if there is an outstanding
  // non-bufferable transfer, this valid response will be postponed to keep the transfer responses in the correct order.
  // The transfer accepted pulse is therefore extended until the pending non-bufferable transfer is finished.
  assign bufferable_resp =  trans_accepted || (bufferable_resp_q && non_bufferable_pending);

  always_comb begin
    outstanding_bufferable_next = outstanding_bufferable_q;

    if (trans_accepted) begin
      // Shift in bufferable bit of accepted transfer
      outstanding_bufferable_next    = outstanding_bufferable_next << 1;
      outstanding_bufferable_next[1] = trans_i.memtype[0];
    end

    // Set high if any outstanding transfers are non-buferable
    non_bufferable_pending  = 0;
    foreach (outstanding_bufferable_q[i]) begin
      if (!outstanding_bufferable_q[i] && (i > 0) && (i <= cnt_q)) begin
        non_bufferable_pending = 1'b1;
      end
    end
  end

  ///////////////////////////////////////////
  // Counter
  ///////////////////////////////////////////
  assign count_up   = trans_accepted;
  assign count_down = resp_valid_i;

  always_comb begin
    next_cnt = cnt_q;
    if (count_up) begin
      next_cnt++;
    end
    if (count_down) begin
      next_cnt--;
    end
  end

  ///////////////////////////////////////////
  // Registers
  ///////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n) begin
    if(rst_n == 1'b0)  begin
      cnt_q                    <= '0;
      bufferable_resp_q        <= 1'b0;
      outstanding_bufferable_q <= '0;
    end else begin
      cnt_q                    <= next_cnt;
      bufferable_resp_q        <= bufferable_resp;
      outstanding_bufferable_q <= outstanding_bufferable_next;
    end
  end

  ///////////////////////////////////////////
  // Filtering
  ///////////////////////////////////////////

  // Blocking transfers when outstanding queue is full to avoid cnt_q overflow
  assign ready_o      = ready_i && (cnt_q < DEPTH);
  assign valid_o      = valid_i && (cnt_q < DEPTH);

  // Response Mux
  // Signals resp_valid early for bufferable transfers and lets resp_valid through when waiting for a non-bufferable transfers
  // The early response for bufferable transfers is gated if we already have an outstanding bufferable transfer to ensure
  // Correct ordering of the responses
  assign resp_valid_o = (resp_is_bufferable) ? bufferable_resp_q && !non_bufferable_pending : resp_valid_i;

  assign trans_o      = trans_i;

endmodule : cv32e40x_lsu_response_filter
