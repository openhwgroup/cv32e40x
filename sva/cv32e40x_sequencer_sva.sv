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
//                                                                            //
// Authors:        Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    RTL assertions for the sequencer module                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_sequencer_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
 #(
   parameter rv32_e    RV32 = RV32I
 )
(
  input  logic           clk,
  input  logic           rst_n,

  input  logic           valid_i,
  input  logic           kill_i,
  input  logic           halt_i,
  input  logic           valid_o,
  input  logic           ready_i,
  input  logic           ready_o,
  input  seq_t           instr_cnt_q,
  input  seq_state_e     seq_state_q,
  input  logic           seq_last_o,
  input  seq_instr_e     seq_instr,
  input  logic           instr_is_tbljmp_ptr_i,
  input  logic           instr_is_clic_ptr_i,
  input  logic           instr_is_mret_ptr_i,
  input  logic           seq_tbljmp_o,
  input  ex_wb_pipe_t    ex_wb_pipe_i,
  input  logic           wb_valid_i,
  input  logic           exception_in_wb_i,
  input  logic           pending_sync_debug_i
);

  // After kill, all state must be reset.
  a_kill_state:
  assert property (@(posedge clk) disable iff (!rst_n)
                    kill_i |=> ((instr_cnt_q == '0) && (seq_state_q == S_IDLE)))
      else `uvm_error("sequencer", "Sequencer state not reset after kill_i.")

  // After sequence is done, all state must be reset.
  a_done_state:
  assert property (@(posedge clk) disable iff (!rst_n)
                    (valid_o && seq_last_o && ready_i) |=> ((instr_cnt_q == '0) && (seq_state_q == S_IDLE)))
      else `uvm_error("sequencer", "Sequencer state not reset after finishing sequence")

  // Kill implies ready and not valid
  a_seq_kill:
  assert property (@(posedge clk) disable iff (!rst_n)
                    kill_i |-> (ready_o && !valid_o))
      else `uvm_error("sequencer", "Kill should imply ready and not valid.")


  // Halt implies not ready and not valid
  a_seq_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (halt_i && !kill_i)
                      |-> (!ready_o && !valid_o))
      else `uvm_error("sequencer", "Halt should imply not ready and not valid")

  // State should not update while halted and not killed
  a_seq_halt_state_stable :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (halt_i && !kill_i)
                      |=> ($stable(instr_cnt_q) && $stable(seq_state_q)))
      else `uvm_error("sequencer", "Counter or state not stable while halted")

  // Check max sequence length
  // POPRETZ with rlist ra, s0-s11
  // 13 register loads
  // 1 stack pointer update
  // 1 clearing of a0
  // 1 return
  // Total sequence length = 16 -> must signal seq_last_o on counter value 'd15
  // For RV32E, max number of register loads is 3 -> total sequence length is 'd6 (counter value is 'd5)
  a_max_seq_len_popretz:
  assert property (@(posedge clk) disable iff (!rst_n)
                  valid_i && (seq_instr == POPRETZ) && (instr_cnt_q == ((RV32 == RV32E) ? 'd5 : 'd15))
                  |->
                  seq_last_o)
      else `uvm_error("sequencer", "popretz sequence too long")

  // Check max sequence length
  // POPRET with rlist ra, s0-s11
  // 13 register loads
  // 1 stack pointer update
  // 1 return
  // Total sequence length = 15
  // For RV32E, max number of register loads is 3 -> total sequence length is 'd5
  a_max_seq_len_popret:
    assert property (@(posedge clk) disable iff (!rst_n)
                    valid_i && (seq_instr == POPRET)
                    |->
                    (instr_cnt_q < ((RV32 == RV32E) ? 'd5 : 'd15)))
        else `uvm_error("sequencer", "popret sequence too long")


  // Check max sequence length
  // POP with rlist ra, s0-s11
  // 13 register loads
  // 1 stack pointer update
  // Total sequence length = 14
  // For RV32E, max number of register loads is 3 -> total sequence length is 'd4
  a_max_seq_len_pop:
    assert property (@(posedge clk) disable iff (!rst_n)
                    valid_i && (seq_instr == POP)
                    |->
                    (instr_cnt_q < ((RV32 == RV32E) ? 'd4 : 'd14)))
        else `uvm_error("sequencer", "pop sequence too long")

  // Check max sequence length
  // PUSH with rlist ra, s0-s11
  // 13 register stores
  // 1 stack pointer update
  // Total sequence length = 14
  // For RV32E, max number of register stores is 3 -> total sequence length is 'd4
  a_max_seq_len_push:
    assert property (@(posedge clk) disable iff (!rst_n)
                    valid_i && (seq_instr == PUSH)
                    |->
                    (instr_cnt_q < ((RV32 == RV32E) ? 'd4 : 'd14)))
        else `uvm_error("sequencer", "push sequence too long")

  // Check max sequence length
  // MVA01S
  // 2 register moves
  a_max_seq_len_mva01s:
  assert property (@(posedge clk) disable iff (!rst_n)
                  valid_i && (seq_instr == MVA01S)
                  |->
                  (instr_cnt_q < 'd2))
      else `uvm_error("sequencer", "mva01s sequence too long")

  // Check max sequence length
  // MVSA01
  // 2 register moves
  a_max_seq_len_mvsa01:
    assert property (@(posedge clk) disable iff (!rst_n)
                    valid_i && (seq_instr == MVSA01)
                    |->
                    (instr_cnt_q < 'd2))
        else `uvm_error("sequencer", "mva01s sequence too long")

  // Check that the sequencer does not decode any instructions from pointers
  a_ptr_illegal:
    assert property (@(posedge clk) disable iff (!rst_n)
                    (instr_is_tbljmp_ptr_i || instr_is_clic_ptr_i || instr_is_mret_ptr_i)
                    |->
                    (seq_instr == INVALID_INST))
        else `uvm_error("sequencer", "Instruction should not be decoded from a pointer")

  // Check that the sequence counter does not count for tablejumps or tablejump pointers
  a_tbljmp_cnt:
    assert property (@(posedge clk) disable iff (!rst_n)
                    (valid_o && ready_i && (seq_tbljmp_o || instr_is_tbljmp_ptr_i))
                    |=>
                    (instr_cnt_q == '0))
        else `uvm_error("sequencer", "Should not count when handling table jumps")


  // Support logic. Sticky bit indicating synchronous exception or syncronous debug during a push or pop sequence
  logic        pushpop_sync_exc_or_dbg_q;

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      pushpop_sync_exc_or_dbg_q <= 1'b0;
    end
    else begin
      if (wb_valid_i && ex_wb_pipe_i.instr_meta.pushpop && ex_wb_pipe_i.first_op) begin
        // Clear pushpop_sync_exc_or_dbg_q when a new push or pop starts
        pushpop_sync_exc_or_dbg_q <= 1'b0;
      end
      else begin
        // Register if there's a synchronous exception or synchronous debug entry
        pushpop_sync_exc_or_dbg_q <= pushpop_sync_exc_or_dbg_q || exception_in_wb_i || pending_sync_debug_i;
      end
    end
  end

  // Check that "end sequence", starting with stack pointer update, is never initiated if there was a synchronous exception or synchronous debug entry earlier in the sequence
  property p_pushpop_sp_update;
    @(posedge clk) disable iff (!rst_n)
      ((ex_wb_pipe_i.instr_meta.pushpop && ex_wb_pipe_i.rf_we && (ex_wb_pipe_i.rf_waddr == 'h2)) // Stack pointer update during push/pop
       |-> !pushpop_sync_exc_or_dbg_q
       );
  endproperty : p_pushpop_sp_update

  a_pushpop_sp_update: assert property(p_pushpop_sp_update) else `uvm_error("controller", "Assertion a_pushpop_sp_update failed");

  // Check that popretz "end sequence", is not interrupted or stalled
  property p_pushpop_atomic_end_sequence_popretz;
  @(posedge clk) disable iff (!rst_n)
    ((wb_valid_i && ex_wb_pipe_i.rf_we && (ex_wb_pipe_i.rf_waddr == 'h2) &&
     (ex_wb_pipe_i.instr.bus_resp.rdata[15:8] == 8'b101_11100) && (ex_wb_pipe_i.instr.bus_resp.rdata[1:0] == 2'b10))                             // Stack pointer update at end of popretz.
     |->
     ##1 wb_valid_i && ex_wb_pipe_i.rf_we && (ex_wb_pipe_i.rf_waddr == 'hA) && (ex_wb_pipe_i.rf_wdata == 'h0) && ex_wb_pipe_i.instr_meta.pushpop // Write 0 to A0 must retire in next cycle
     ##1 wb_valid_i && ex_wb_pipe_i.rf_we && ex_wb_pipe_i.alu_jmp_qual                                        && ex_wb_pipe_i.instr_meta.pushpop // Jump in WB
     );
  endproperty : p_pushpop_atomic_end_sequence_popretz

  a_pushpop_atomic_end_sequence_popretz: assert property(p_pushpop_atomic_end_sequence_popretz) else `uvm_error("controller", "Assertion a_pushpop_atomic_end_sequence_popretz failed");

  // Check that popret "end sequence", is not interrupted or stalled
  property p_pushpop_atomic_end_sequence_popret;
  @(posedge clk) disable iff (!rst_n)
    ((wb_valid_i && ex_wb_pipe_i.rf_we && (ex_wb_pipe_i.rf_waddr == 'h2) &&
     (ex_wb_pipe_i.instr.bus_resp.rdata[15:8] == 8'b101_11110) && (ex_wb_pipe_i.instr.bus_resp.rdata[1:0] == 2'b10)) // Stack pointer update at end of popret.
     |->
     ##1 1'b1                                                                                                        // We'll always have a bubble becuase the jump is stalled due to RA write in WB (before stack pointer update)
     ##1 wb_valid_i && ex_wb_pipe_i.rf_we && ex_wb_pipe_i.alu_jmp_qual && ex_wb_pipe_i.instr_meta.pushpop            // Jump in WB
     );
  endproperty : p_pushpop_atomic_end_sequence_popret

  a_pushpop_atomic_end_sequence_popret: assert property(p_pushpop_atomic_end_sequence_popret) else `uvm_error("controller", "Assertion a_pushpop_atomic_end_sequence_popret failed");

endmodule
