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
   input logic [13:0]      rvfi_trap,
   input logic [2:0]       rvfi_dbg,

   input                   ctrl_fsm_t ctrl_fsm_i,
   input logic [31:0]      rvfi_csr_dcsr_rdata,
   input logic [31:0]      rvfi_csr_mcause_rdata,
   input logic [31:0]      rvfi_pc_rdata,
   input logic [31:0]      nmi_addr_i,
   
   input logic             irq_ack,
   input logic             dbg_ack,
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
  assign debug_cause_int = ebreak_in_wb_i ? 3'h1 : ctrl_fsm_i.debug_cause;

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


  // Sequence used to locate rvfi_valid following rvfi_valid with prereq set
  sequence s_goto_next_rvfi_valid(prereq);
    (prereq && rvfi_valid) ##1 rvfi_valid[->1];
  endsequence

  logic no_debug;

  // Indicate debug mode, or single stepping
  assign no_debug = !(rvfi_csr_dcsr_rdata[2] || ctrl_fsm_i.debug_mode);

  // rvfi_trap should always be followed by rvfi_intr (as long as we're not in debug mode)
  a_rvfi_trap_intr :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     no_debug throughout s_goto_next_rvfi_valid(|rvfi_trap) |->
                     rvfi_intr)
      else `uvm_error("rvfi", "rvfi_trap not followed by rvfi_intr")

  // rvfi_trap[2] should always be followed by rvfi_dbg
  a_rvfi_trap_dbg :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     s_goto_next_rvfi_valid(rvfi_trap[2]) |->
                     rvfi_dbg != '0)
      else `uvm_error("rvfi", "rvfi_trap[2] not followed by rvfi_dbg")

  // Exception code in rvfi_trap[8:3] should align with mcause exception cause in the following retired instruction
  // This is exempt if we have an NMI, because NMI will result in mcause being updated in between retired instructions.
  // Also, in debug mode, mcause is not updated.
  a_rvfi_trap_mcause_align:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                    (no_debug && !ctrl_fsm_i.pending_nmi) throughout s_goto_next_rvfi_valid(|rvfi_trap) |->
                     rvfi_intr && (rvfi_csr_mcause_rdata[5:0] == $past(rvfi_trap[8:3])))
      else `uvm_error("rvfi", "rvfi_trap[8:3] not consistent with mcause[5:0] in following retired instruction")

  // Exception code in rvfi_trap[11:9] should align with rvfi_dbg the following retired instruction
  a_rvfi_trap_rvfi_dbg_align:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     s_goto_next_rvfi_valid(rvfi_trap[2]) |->
                     rvfi_dbg == $past(rvfi_trap[11:9]))
     else `uvm_error("rvfi", "rvfi_trap[11:9] not consistent with rvfi_dbg in following retired instruction")

  // Check that rvfi_trap always indicate single step if rvfi_trap[2:1] == 2'b11
  a_rvfi_single_step_trap:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     rvfi_trap[1] && rvfi_trap[2] |-> rvfi_trap[11:9] == DBG_CAUSE_STEP)
     else `uvm_error("rvfi", "rvfi_trap[2:1] == 2'b11, but debug cause bits do not indicate single stepping")

  // Check that the trap is always signalled on the instruction before single step debug entry (unless killed by interrupt)
  a_rvfi_single_step_no_trap_no_dbg_entry:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     s_goto_next_rvfi_valid(rvfi_trap[11:9] != DBG_CAUSE_STEP) |-> ((rvfi_dbg != DBG_CAUSE_STEP) || rvfi_intr))
     else `uvm_error("rvfi", "Single step debug entry without correct rvfi_trap first")

  // Check that dcsr.cause and mcause exception align with rvfi_trap when rvfi_trap[2:1] == 2'b11
  // rvfi_intr should also always be set in this case
  a_rvfi_trap_step_exception:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     s_goto_next_rvfi_valid(rvfi_trap[1] && rvfi_trap[2]) |->
                     (rvfi_dbg == DBG_CAUSE_STEP) && (rvfi_csr_dcsr_rdata[8:6] == DBG_CAUSE_STEP) &&
                     (rvfi_csr_mcause_rdata[5:0] == $past(rvfi_trap[8:3])) &&
                     rvfi_intr)
     else `uvm_error("rvfi", "dcsr.cause, mcause and rvfi_intr not as expected following an exception during single step")

  // When dcsr.nmip is set, the next retired instruction should be the NMI handler (except in debug mode).
  // rvfi_intr should also be set.
  a_rvfi_nmip_nmi_handler:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (no_debug && $stable(nmi_addr_i)) throughout s_goto_next_rvfi_valid(rvfi_csr_dcsr_rdata[3]) |->
                     rvfi_intr &&
                     (rvfi_pc_rdata == {nmi_addr_i[31:2], 2'b00}) &&
                     ((rvfi_csr_mcause_rdata[7:0] == INT_CAUSE_LSU_LOAD_FAULT) || (rvfi_csr_mcause_rdata[7:0] == INT_CAUSE_LSU_STORE_FAULT)))
      else `uvm_error("rvfi", "dcsr.nmip not followed by rvfi_intr and NMI handler")

endmodule : cv32e40x_rvfi_sva


