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
// Description:    MPU (Memory Protection Unit) assertions                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_mpu_sva import cv32e40x_pkg::*; import uvm_pkg::*;
  #(  parameter int unsigned PMA_NUM_REGIONS              = 0,
      parameter pma_region_t PMA_CFG[(PMA_NUM_REGIONS ? (PMA_NUM_REGIONS-1) : 0):0] = '{default:PMA_R_DEFAULT},
      parameter int unsigned IS_INSTR_SIDE = 0)
  (
   input logic        clk,
   input logic        rst_n,
   
   input logic        speculative_access_i,
   input logic        atomic_access_i,
   input logic        execute_access_i,
   input logic        bus_trans_bufferable,
   input logic        bus_trans_cacheable,

   // PMA signals
   input logic        pma_err,
   input logic [31:0] pma_addr,
   input pma_region_t pma_cfg,

   // Core OBI signals
   input logic [ 1:0] obi_memtype,
   input logic [31:0] obi_addr,
   input logic        obi_req,
   input logic        obi_gnt,

   // Interface towards bus interface
   input logic        bus_trans_ready_i,
   input logic        bus_trans_valid_o,
  
   input logic        bus_resp_valid_i,

   // Interface towards core
   input logic        core_trans_valid_i,
   input logic        core_trans_ready_o,
   
   input logic        core_resp_valid_o,

   input              mpu_status_e mpu_status,
   input logic        mpu_err_trans_valid,
   input logic        mpu_block_core,
   input logic        mpu_block_bus,
   input              mpu_state_e state_q,
   input logic        mpu_err
   );


  // PMA assertions helper signals

  logic is_addr_match;
  assign is_addr_match = obi_addr == pma_addr;

  logic was_obi_waiting;
  logic was_obi_reqnognt;
  assign was_obi_waiting = was_obi_reqnognt && !bus_trans_ready_i;
  always @(posedge clk) begin
    was_obi_reqnognt <= 0;
    if (rst_n) was_obi_reqnognt <= obi_req && !obi_gnt;
  end

  logic is_lobound_ok;
  logic is_hibound_ok;
  assign is_lobound_ok = {pma_cfg.word_addr_low, 2'b00} <= pma_addr;
  assign is_hibound_ok = pma_addr < {pma_cfg.word_addr_high, 2'b00};

  logic is_pma_matched;
  int   pma_match_num;
  int   pma_lowest_match;
  always_comb begin
    is_pma_matched = 0;
    pma_match_num = 999;
    pma_lowest_match = 999;

    // Find pma module's attributes among cfgs
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if (pma_cfg == PMA_CFG[i]) begin
        is_pma_matched = 1;
        pma_match_num = i;
        break;
      end
    end

    // Find lowest region matching addr
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if (({PMA_CFG[i].word_addr_low, 2'b00} <= pma_addr) && (pma_addr < {PMA_CFG[i].word_addr_high, 2'b00})) begin
        pma_lowest_match = i;
        break;
      end
    end
  end
  cov_pma_matchnone : cover property (@(posedge clk) disable iff (!rst_n) (!is_pma_matched));
  cov_pma_matchfirst : cover property (@(posedge clk) disable iff (!rst_n) (is_pma_matched && (pma_match_num == 0)));
  cov_pma_matchother : cover property (@(posedge clk) disable iff (!rst_n) (is_pma_matched && (pma_match_num > 0)));


  // Checks for illegal PMA region configuration

  initial begin : p_mpu_assertions
    if (PMA_NUM_REGIONS != 0) begin
      assert (PMA_NUM_REGIONS == $size(PMA_CFG)) else `uvm_error("mpu", "PMA_CFG must contain PMA_NUM_REGION entries")
    end
      
    for(int i=0; i<PMA_NUM_REGIONS; i++) begin
      if (PMA_CFG[i].main) begin
        assert (PMA_CFG[i].atomic) else `uvm_error("mpu", "PMA regions configured as main must also support atomic operations")
      end

      if (!PMA_CFG[i].main) begin
        assert (!PMA_CFG[i].cacheable) else `uvm_error("mpu", "PMA regions configured as I/O cannot be defined as cacheable")
      end
    end
  end

  a_pma_valid_num_regions :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (0 <= PMA_NUM_REGIONS) && (PMA_NUM_REGIONS <= 16))
      else `uvm_error("mpu", "PMA number of regions is badly configured")

  // Region matching
  a_pma_match_bounds :
    assert property (@(posedge clk) disable iff (!rst_n)
                     is_pma_matched |-> (is_lobound_ok && is_hibound_ok))
      else `uvm_error("mpu", "PMA region match doesn't fit bounds")
  a_pma_match_lowest :
    assert property (@(posedge clk) disable iff (!rst_n)
                     is_pma_matched |-> (pma_match_num == pma_lowest_match))
      else `uvm_error("mpu", "PMA region match wasn't lowest")
  a_pma_match_index :
    assert property (@(posedge clk) disable iff (!rst_n)
                     is_pma_matched |-> ((0 <= pma_match_num) && (pma_match_num <= 16)))
      else `uvm_error("mpu", "illegal cfg index")

  // Bufferable
  a_pma_obi_bufrequired :
    assert property (@(posedge clk) disable iff (!rst_n)
                     bus_trans_bufferable
                     |-> obi_memtype[0] ^ (!obi_memtype[0] && was_obi_waiting && !$past(obi_memtype[0])))
      else `uvm_error("mpu", "obi should have had bufferable flag")
  a_pma_obi_bufallowed :
    assert property (@(posedge clk) disable iff (!rst_n)
                     obi_memtype[0]
                     |-> bus_trans_bufferable ^ (!bus_trans_bufferable && was_obi_waiting && $past(obi_memtype[0])))
      else `uvm_error("mpu", "obi should not have had bufferable flag")

  // Cacheable
  a_pma_obi_cacherequired :
    assert property (@(posedge clk) disable iff (!rst_n)
                     bus_trans_cacheable
                     |-> obi_memtype[1] ^ (!obi_memtype[1] && was_obi_waiting && !$past(obi_memtype[1])))
      else `uvm_error("mpu", "obi should have had cacheable flag")
  a_pma_obi_cacheallowed :
    assert property (@(posedge clk) disable iff (!rst_n)
                     obi_memtype[1]
                     |-> bus_trans_cacheable ^ (!bus_trans_cacheable && was_obi_waiting && $past(obi_memtype[1])))
      else `uvm_error("mpu", "obi should not have had cacheable flag")

  // OBI req vs PMA err
  a_pma_obi_reqallowed :
    assert property (@(posedge clk) disable iff (!rst_n)
                     obi_req
                     |->
                     (!pma_err && is_addr_match)
                     ^ (!is_addr_match && was_obi_waiting && $past(obi_req)))
      else `uvm_error("mpu", "obi made request to pma-forbidden region")
  a_pma_obi_reqdenied :
    assert property (@(posedge clk) disable iff (!rst_n)
                     pma_err
                     |-> !obi_req ^ (was_obi_waiting && $past(obi_req)))
      else `uvm_error("mpu", "pma error should forbid obi req")


  // Cover PMA signals

  covergroup cg_pma @(posedge clk);
    cp_err: coverpoint pma_err;
    cp_exec: coverpoint execute_access_i;
    cp_bufferable: coverpoint bus_trans_bufferable;
    cp_cacheable: coverpoint bus_trans_cacheable;
    cp_atomic: coverpoint atomic_access_i;
    cp_addr: coverpoint pma_addr[31:2] {
      bins min = {0};
      bins max = {30'h 3FFF_FFFF};
      bins range[3] = {[1 : 30'h 3FFF_FFFe]};
      illegal_bins il = default;
      }

    x_err_exec: cross cp_err, cp_exec;
    x_err_bufferable: cross cp_err, cp_bufferable;
    x_err_cacheable: cross cp_err, cp_cacheable;
    x_err_atomic: cross cp_err, cp_atomic;
  endgroup
  cg_pma cgpma = new;

  cov_pma_nondefault :
    cover property (@(posedge clk) disable iff (!rst_n)
      (pma_cfg != PMA_R_DEFAULT) && bus_trans_valid_o);


  // Should only give MPU error response during mpu_err_trans_valid
  a_mpu_status_no_obi_rvalid :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (mpu_status != MPU_OK) |-> (mpu_err_trans_valid) )
      else `uvm_error("mpu", "MPU error status wile not mpu_err_trans_valid")

  // MPU FSM and bus interface should never assert trans valid at the same time
  a_mpu_bus_mpu_err_valid :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (! (bus_resp_valid_i && mpu_err_trans_valid) ))
      else `uvm_error("mpu", "MPU FSM and bus interface response collision")

  // Should only block core side upon when waiting for MPU error response
  a_mpu_block_core_iff_wait :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (mpu_block_core) |-> (state_q != MPU_IDLE) )
      else `uvm_error("mpu", "MPU blocking core side when not needed")

  // Should only block OBI side upon MPU error
  a_mpu_block_bus_iff_err :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (mpu_block_bus) |-> (mpu_err || (state_q != MPU_IDLE)) )
      else `uvm_error("mpu", "MPU blocking OBI side when not needed")

endmodule : cv32e40x_mpu_sva

