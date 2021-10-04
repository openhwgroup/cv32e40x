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
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    Assertions for RVFI                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_rvfi_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  import cv32e40x_rvfi_pkg::*;
  (
   input logic             clk_i,
   input logic             rst_ni,

   input logic             rvfi_valid,
   input logic             rvfi_intr,
   input logic [2:0]       rvfi_dbg,
   
   input logic             irq_ack,
   input logic             dbg_ack,
   input logic [2:0]       ctrl_fsm_debug_cause,
   input logic             ebreak_in_wb_i,
   
   input logic [3:0]       in_trap,
   input logic [3:0] [2:0] debug_cause
   );
  
  // Check that irq_ack results in RVFI capturing a trap
  // Ideally, we should assert that every irq_ack eventually leads to rvfi_intr,
  // but since there can be an infinite delay between irq_ack and rvfi_intr (e.g. because of bus stalls), we're settling for asserting
  // that irq_ack leads to RVFI capturing a trap (in_trap[IF_STAGE] = 1)
  a_irq_ack_rvfi_capture :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (irq_ack |=> in_trap[STAGE_IF]))
      else `uvm_error("rvfi", "irq_ack not captured by RVFI")

   
  // Helper signal, indicating debug cause
  // Special case for debug entry from debug mode caused by EBREAK as it is not captured by debug_cause_i
  logic [2:0] debug_cause_int;
  assign debug_cause_int = ebreak_in_wb_i ? 3'h1 : ctrl_fsm_debug_cause;

  // Check that dbg_ack results in RVFI capturing a debug_cause
  // Ideally, we should assert that every dbg_ack eventually leads to rvfi_dbg,
  // but since there can be an infinite delay between dbg_ack and rvfi_dbg (e.g. because of bus stalls), we're settling for asserting
  // that dbg_ack leads to RVFI capturing the debug cause
  a_dbg_ack_rvfi_capture :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (dbg_ack |=> (debug_cause[STAGE_IF] == $past(debug_cause_int))))
            else `uvm_error("rvfi", "dbg_ack did not lead to rvfi_dbg != 0")

    
    
  // Helper signal, indicate that a debug entry was signaled on RVFI
  logic  rvfi_dbg_ack;
  assign rvfi_dbg_ack = |rvfi_dbg && rvfi_valid;

  // Helper signal, count outstanding dbg_ack
  bit [1:0] dbg_ack_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dbg_ack_cnt <= '0;
    end
    else begin
      if (dbg_ack && !rvfi_dbg_ack) begin
        dbg_ack_cnt <= dbg_ack_cnt+1;
      end
      else if (rvfi_dbg_ack && !dbg_ack) begin
        dbg_ack_cnt <= dbg_ack_cnt-1;
      end
    end
  end
  
  // Check that rvfi_dbg_ack is preceeded by dbg_ack
  a_rvfi_dbg_dbg_ack :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (rvfi_dbg_ack |-> (dbg_ack_cnt != 0)))
      else `uvm_error("rvfi", "rvfi_dbg not preceeded by dbg_ack")
    
endmodule : cv32e40x_rvfi_sva


