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
// Authors:        Halfdan Bechmann - Halfdan Bechmann@silabs.com             //
//                                                                            //
// Description:    Write Buffer assertions                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_write_buffer_sva
  import cv32e40x_pkg::*;
  import uvm_pkg::*;
  (input logic          clk,
   input logic          rst_n,

   input logic          ready_i,
   input logic          valid_i,
   input obi_data_req_t trans_i,

   input logic          state,
   input obi_data_req_t trans_q,
   input logic          bufferable,

   input logic          valid_o,
   input logic          ready_o,
   input obi_data_req_t trans_o
   );


  // Track pending transaction
  logic               waited_addr_ph;
  always_ff @(posedge clk, negedge rst_n) begin
    if(!rst_n) begin
      waited_addr_ph <= 1'b0;
    end else begin
      waited_addr_ph <= valid_o && !ready_i;
    end
  end

  ///////////////////////////////////////////
  // Verify OBI protocol adherence
  ///////////////////////////////////////////
  // verify that valid_o is held during waited addr phase
  property p_valid_o_held_during_waited_addr_ph;
    @(posedge clk)
      waited_addr_ph |-> (valid_o === 1'b1);
  endproperty : p_valid_o_held_during_waited_addr_ph

  a_valid_o_held_during_waited_addr_ph: assert property (p_valid_o_held_during_waited_addr_ph)
    else `uvm_error("write_buffer", "valid_o is retracted during waited address phase");

  // verify that data_o remains stable during waited addr phase
  property p_data_o_stable_during_waited_addr_ph;
    @(posedge clk)
      waited_addr_ph |-> $stable(trans_o);
  endproperty : p_data_o_stable_during_waited_addr_ph

  a_data_o_stable_during_waited_addr_ph: assert property (p_data_o_stable_during_waited_addr_ph)
    else `uvm_error("write_buffer", "trans_o is not stable during waited address phase");


  ///////////////////////////////////////////////////
  // Verify that incoming data is buffered properly
  ///////////////////////////////////////////////////
  property p_data_q_value;
    @(posedge clk)
      bufferable && (state === WBUF_EMPTY) && (valid_i && !ready_i) |=> (trans_q === $past(trans_i));
  endproperty : p_data_q_value

  a_data_q_value: assert property (p_data_q_value)
    else `uvm_error("write_buffer", "trans_q is should have been same as trans_i from previous edge");

  // When trans_q is changed, the state should transit from EMPTY to FULL
  property p_data_q_condition;
    @(posedge clk)
      ##1 (trans_q !== $past(trans_q)) |-> (state === WBUF_FULL) && ($past(bufferable) && ($past(state) === WBUF_EMPTY) && ($past(valid_i) && !$past(ready_i))); // ##1 used to avoid first clock edge when past data_q value is unknown
      endproperty : p_data_q_condition

  a_data_q_condition: assert property (p_data_q_condition)
    else `uvm_error("write_buffer", "trans_q is pushed when proper condition is not met");


  ///////////////////////////////////////////////////
  // verify output generation
  ///////////////////////////////////////////////////
  // ready_o should be 1 only when state is EMPTY
  property p_ready_o_one;
    @(posedge clk)
      ready_o |-> (state === WBUF_EMPTY);
  endproperty : p_ready_o_one

  a_ready_o_one: assert property (p_ready_o_one)
    else `uvm_error("write_buffer", "When ready_o is 1, state should be EMPTY");

  // ready_o should be 0 only when state is FULL if the transfer is bufferable
  property p_ready_o_zero;
    @(posedge clk)
      bufferable && !ready_o |-> (state === WBUF_FULL);
  endproperty : p_ready_o_zero

  a_ready_o_zero: assert property (p_ready_o_zero)
    else `uvm_error("write_buffer", "For bufferable transfers, when ready_o is 0, state should be FULL");

  // When state is FULL, data_o should come from trans_q
  property p_trans_o_full;
    @(posedge clk)
      (state === WBUF_FULL) |-> (trans_o === trans_q);
  endproperty : p_trans_o_full

  a_trans_o_full: assert property (p_trans_o_full)
    else `uvm_error("write_buffer", "When state is FULL, trans_o should come from trans_q");

  // When state is EMPTY, trans_o should come from trans_i
  property p_trans_o_empty;
    @(posedge clk)
      (state === WBUF_EMPTY) |-> (trans_o === trans_i);
  endproperty : p_trans_o_empty

  a_trans_o_empty: assert property (p_trans_o_empty)
    else `uvm_error("write_buffer", "When state is EMPTY, trans_o should come from trans_i");

endmodule : cv32e40x_write_buffer_sva
