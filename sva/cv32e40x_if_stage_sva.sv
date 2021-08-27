// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Renzo Andri - andrire@student.ethz.ch                      //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the if_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_if_stage_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
(
  input  logic          clk,
  input  logic          rst_n,

  input logic           if_ready,
  input logic           if_valid_o,  
  input  ctrl_fsm_t     ctrl_fsm_i,
  if_c_obi.monitor      m_c_obi_instr_if
);

  // Check that bus interface transactions are word aligned
  property p_instr_addr_word_aligned;
    @(posedge clk) (1'b1) |-> (m_c_obi_instr_if.req_payload.addr[1:0] == 2'b00);
  endproperty

  a_instr_addr_word_aligned : assert property(p_instr_addr_word_aligned)
    else `uvm_error("if_stage", "Assertion a_instr_addr_word_aligned failed")

  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_if && !ctrl_fsm_i.kill_if)
                      |-> (!if_ready && !if_valid_o))
      else `uvm_error("if_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_if)
                      |-> (if_ready && !if_valid_o))
      else `uvm_error("if_stage", "Kill should imply ready and not valid")


endmodule // cv32e40x_if_stage

