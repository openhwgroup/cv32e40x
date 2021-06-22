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
// Authors:        Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Description:    RTL assertions for the wb_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_wb_stage_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
(
  input logic           clk,
  input logic           rst_n,
   
  input logic           wb_ready_o,
  input logic           wb_valid,  
  input ctrl_fsm_t      ctrl_fsm_i,
  input ex_wb_pipe_t    ex_wb_pipe_i
);

  // LSU instructions should not get killed once in WB (as they commit already in EX).
  a_lsu_no_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid)
                      |-> (!ctrl_fsm_i.kill_wb))
      else `uvm_error("wb_stage", "LSU instruction killed in WB")


// todo: Discuss whether we want early write enable suppression or not
//
//  // Check that registered 'write enable' type signals have already been suppressed if
//  // registered instr_valid = 0.
//  property p_early_write_enable_suppression;
//    @(posedge clk) disable iff (!rst_n)
//      (ex_wb_pipe_i.instr_valid == 1'b0) |-> ((ex_wb_pipe_i.rf_we == 1'b0) && (ex_wb_pipe_i.lsu_en == 1'b0));
//  endproperty
//
//  a_early_write_enable_suppression : assert property(p_early_write_enable_suppression) else `uvm_error("wb_stage", "Write enables not suppressed yet")



  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_wb)
                      |-> (!wb_ready_o && !wb_valid))
      else `uvm_error("wb_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_wb)
                      |-> (wb_ready_o && !wb_valid))
      else `uvm_error("wb_stage", "Kill should imply ready and not valid")

  // Never kill and halt at the same time (as they have conflicting requirements on ready)
  a_kill_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_wb)
                      |-> (!ctrl_fsm_i.halt_wb))
      else `uvm_error("wb_stage", "Kill and halt should not both be asserted")

endmodule // cv32e40x_wb_stage_sva
