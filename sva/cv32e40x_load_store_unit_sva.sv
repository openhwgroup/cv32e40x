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
// Authors:        Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the load_store_unit module              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_load_store_unit_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  #(parameter DEPTH = 0)
  (input logic       clk,
   input logic       rst_n,
   input logic [1:0] cnt_q,
   input logic       busy_o,
   input logic       count_up,
   input logic       count_down,
   input ctrl_fsm_t  ctrl_fsm_i,
   input logic       trans_valid,
   input logic       split_q,
   input mpu_status_e lsu_mpu_status_1_o, // WB mpu status
   input ex_wb_pipe_t ex_wb_pipe_i,
   if_c_obi.monitor  m_c_obi_data_if);

  // Check that outstanding transaction count will not overflow DEPTH
  property p_no_transaction_count_overflow_0;
    @(posedge clk) (1'b1) |-> (cnt_q <= DEPTH);
  endproperty

  a_no_transaction_count_overflow_0 :
    assert property(p_no_transaction_count_overflow_0)
      else `uvm_error("load_store_unit", "Assertion a_no_transaction_count_overflow_0 failed")

  property p_no_transaction_count_overflow_1;
        @(posedge clk) (cnt_q == DEPTH) |-> (!count_up || count_down);
  endproperty

  a_no_transaction_count_overflow_1 :
    assert property(p_no_transaction_count_overflow_1)
      else `uvm_error("load_store_unit", "Assertion a_no_transaction_count_overflow_1 failed")

  a_no_cnt_underflow :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (cnt_q == 0) |=> (cnt_q == 0) || (cnt_q == 1))
      else `uvm_error("load_store_unit", "Transfer counter underflow");

  a_busy_when_lsu_outststanding :
   assert property (@(posedge clk) disable iff (!rst_n)
                    (cnt_q != 0) |-> busy_o )
      else `uvm_error("load_store_unit", "Outstanding transfers but LSU busy signal not set")

    // Outstanding Transactions on OBI interface

    int outstanding_cnt;
    int outstanding_cnt_q;
    always_comb begin
      outstanding_cnt = outstanding_cnt_q;
      if (m_c_obi_data_if.s_req.req && m_c_obi_data_if.s_gnt.gnt)
        outstanding_cnt++;
      if (m_c_obi_data_if.s_rvalid.rvalid)
        outstanding_cnt--;
    end

    always_ff @(posedge clk, negedge rst_n) begin
      if (rst_n == 1'b0) begin
        outstanding_cnt_q <= 0;
      end else begin
        outstanding_cnt_q <= outstanding_cnt;
      end
    end

  a_data_obi_max_2_outstanding_transactions :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (outstanding_cnt_q <= 2))
      else `uvm_error("core", "More than two outstanding transactions")

  // Check that an rvalid only occurs when there are outstanding transaction(s)
  property p_no_spurious_rvalid;
        @(posedge clk) (m_c_obi_data_if.s_rvalid.rvalid == 1'b1) |-> (outstanding_cnt_q > 0);
  endproperty

  a_no_spurious_rvalid :
    assert property(p_no_spurious_rvalid) else `uvm_error("load_store_unit", "Assertion a_no_spurious_rvalid failed")

  // Check that the address/we/be/atop does not contain X when request is sent
  property p_address_phase_signals_defined;
      @(posedge clk) (m_c_obi_data_if.s_req.req == 1'b1) |->
                     (!($isunknown(m_c_obi_data_if.req_payload.addr) ||
                        $isunknown(m_c_obi_data_if.req_payload.we)   ||
                        $isunknown(m_c_obi_data_if.req_payload.be)   ||
                        $isunknown(m_c_obi_data_if.req_payload.atop)));
  endproperty

  a_address_phase_signals_defined :
    assert property(p_address_phase_signals_defined)
      else `uvm_error("load_store_unit", "Assertion a_address_phase_signals_defined failed")

  // No transaction allowd if EX is halted or killed
  a_lsu_halt_kill:
    assert property (@(posedge clk) disable iff (!rst_n)
                    (ctrl_fsm_i.kill_ex || ctrl_fsm_i.halt_ex)
                    |-> !trans_valid)
      else `uvm_error("load_store_unit", "Transaction happened while WB is halted or killed")

  // Second half of a split transaction should never get killed while in EX
  // Exception: Second half of a split transaction may be killed if the first half
  //            gets blocked by the PMA.
  a_lsu_no_kill_second_half_ex:
  assert property (@(posedge clk) disable iff (!rst_n)
                  (split_q && (lsu_mpu_status_1_o == MPU_OK)) |-> !ctrl_fsm_i.kill_ex)
    else `uvm_error("load_store_unit", "Second half of split transaction was killed")

  // cnt_q == 2'b00 shall be the same as !(ex_wb_pipe.lsu_en && ex_wb_pipe_i.instr_valid)
  a_cnt_zero:
  assert property (@(posedge clk) disable iff (!rst_n)
                    (cnt_q == 2'b00) |-> !(ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid))
      else `uvm_error("load_store_unit", "cnt_q is zero when WB contains a valid LSU instruction")

endmodule // cv32e40x_load_store_unit_sva

  
