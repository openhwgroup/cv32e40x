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
// Design Name:    Prefetcher Controller                                      //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Controller which receives control flow            //
//                 information (req_i, branch_*) from the Fetch stage         //
//                 and based on that performs transactions requests to the    //
//                 bus interface adapter instructions. Prefetching based on   //
//                 incrementing addressed is performed when no new control    //
//                 flow change is requested. New transaction requests are     //
//                 only performed if it can be guaranteed that the fetch FIFO //
//                 will not overflow (resulting in a maximum of DEPTH         //
//                 outstanding transactions.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_prefetch_controller
(
  input  logic                     clk,
  input  logic                     rst_n,

  input  logic                     branch_i,                // Taken branch
  input  logic [31:0]              branch_addr_i,           // Taken branch address (only valid when branch_i = 1)

  // Transaction request interface
  output logic                     trans_valid_o,           // Transaction request valid (to bus interface adapter)
  input  logic                     trans_ready_i,           // Transaction request ready (transaction gets accepted when trans_valid_o and trans_ready_i are both 1)
  output logic [31:0]              trans_addr_o,            // Transaction address (only valid when trans_valid_o = 1). No stability requirements.

  // Transaction response interface
  input  logic                     resp_valid_i,            // Note: Consumer is assumed to be 'ready' whenever resp_valid_i = 1

  // Fetch interface
  output logic                     fetch_valid_o,
  input  logic                     trans_req_i,
  output logic                     trans_ack_o
);

  import cv32e40x_pkg::*;

  prefetch_state_e state_q, next_state;

  // Transaction address
  logic [31:0]                   trans_addr_q, trans_addr_incr;

  // Word-aligned branch target address
  logic [31:0]                   aligned_branch_addr;             // Word aligned branch target address


  //////////////////////////////////////////////////////////////////////////////
  // IF/ID interface
  //////////////////////////////////////////////////////////////////////////////

  // Fectch valid control. Feed through resp_valid
  assign fetch_valid_o = resp_valid_i;

  // Prefetcher will only perform word fetches
  assign aligned_branch_addr = {branch_addr_i[31:2], 2'b00};

  // Increment address (always word fetch)
  assign trans_addr_incr = {trans_addr_q[31:2], 2'b00} + 32'd4;

  // Transaction request generation
  // Avoid combinatorial path from instr_rvalid_i to instr_req_o. Multiple trans_* transactions can be 
  // issued (and accepted) before a response (resp_*) is received.
  assign trans_valid_o = trans_req_i;

  assign trans_ack_o = trans_valid_o && trans_ready_i;

  // FSM (state_q, next_state) to control OBI A channel signals.
  always_comb
  begin
    next_state = state_q;
    trans_addr_o = trans_addr_q;

    case(state_q)
      // Default state (pass on branch target address or transaction with incremented address)
      IDLE:
      begin
        begin
          if (branch_i) begin
            // Jumps must have the highest priority (e.g. an interrupt must
            // have higher priority than a HW-loop branch)
            trans_addr_o = aligned_branch_addr;
          end else begin
            trans_addr_o = trans_addr_incr;
          end
        end
        if ((branch_i) && !(trans_valid_o && trans_ready_i)) begin
          // Taken branch, but transaction not yet accepted by bus interface adapter.
          next_state = BRANCH_WAIT;
        end
      end // case: IDLE

      BRANCH_WAIT:
      begin
        // Replay previous branch target address (trans_addr_q) or new branch address (this can
        // occur if for example an interrupt is taken right after a taken jump which did not
        // yet have its target address accepted by the bus interface adapter.
        trans_addr_o = branch_i ? aligned_branch_addr : trans_addr_q;
        if (trans_valid_o && trans_ready_i) begin
          // Transaction with branch target address has been accepted. Start regular prefetch again.
          next_state = IDLE;
        end
      end // case: BRANCH_WAIT
    endcase
  end

  
  //////////////////////////////////////////////////////////////////////////////
  // Registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      state_q        <= IDLE;
      trans_addr_q   <= '0;
    end
    else
    begin
      state_q        <= next_state;
      if (branch_i || (trans_valid_o && trans_ready_i)) begin
        trans_addr_q <= trans_addr_o;
      end
    end
  end

endmodule // cv32e40x_prefetch_controller
