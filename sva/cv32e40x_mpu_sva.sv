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
      parameter pma_region_t PMA_CFG[(PMA_NUM_REGIONS ? (PMA_NUM_REGIONS-1) : 0):0] = '{default:PMA_R_DEFAULT})
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
   input logic [1:0]  instr_memtype_o,

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
    assert property (@(posedge clk)
                     (0 <= PMA_NUM_REGIONS) && (PMA_NUM_REGIONS <= 16))
      else `uvm_error("mpu", "PMA number of regions is badly configured")

  a_pma_region_match :
    assert property (@(posedge clk)
                     !pma_err
                     |->
                     ({pma_cfg.word_addr_low, 2'b00} <= pma_addr)
                     && (pma_addr < {pma_cfg.word_addr_high, 2'b00}))
                     //TODO split in two properties?
      else `uvm_error("mpu", "PMA region match doesn't fit the bounds")

  a_pma_obi_nonbufferable :
    assert property (@(posedge clk)
                     !bus_trans_bufferable |-> !instr_memtype_o[0])  // TODO is this logic "waterproof"?
      else `uvm_error("mpu", "instr OBI erronously flagged as bufferable")
      //TODO also make "a_pma_obi_bufferable"?

  a_pma_obi_cacheable :
    assert property (@(posedge clk)
                     // TODO need "req" condition?
                     bus_trans_cacheable |-> instr_memtype_o[1])
      else `uvm_error("mpu", "instr OBI should have been cacheable")

  a_pma_obi_noncacheable :
    assert property (@(posedge clk)
                     !bus_trans_cacheable |-> !instr_memtype_o[1])  // TODO use XNOR for equivalence checking?
      else `uvm_error("mpu", "instr OBI was erronously cacheable")


  // Cover PMA signals

  covergroup cg_pma @(posedge clk);
    cp_err: coverpoint pma_err;
    cp_exec: coverpoint execute_access_i;  // TODO what about instr side?
    //TODO "cp_speculative"?
    cp_bufferable: coverpoint bus_trans_bufferable;  // TODO is bus_trans right?
    cp_cacheable: coverpoint bus_trans_cacheable;  // TODO is bus_trans right?
    cp_atomic: coverpoint atomic_access_i;
    cp_addr: coverpoint pma_addr[31:2] {  // TODO check if spec justifies this
      bins min = {0};
      bins max = {30'h 3FFF_FFFF};
      bins range[3] = {[1 : 30'h 3FFF_FFFe]};
      illegal_bins il = default;
      }

    //TODO crosses
  endgroup

  cg_pma cgpma = new;


  // Should only give MPU error response during mpu_err_trans_valid
  a_mpu_status_no_obi_rvalid :
    assert property (@(posedge clk)
                     (mpu_status != MPU_OK) |-> (mpu_err_trans_valid) )
      else `uvm_error("mpu", "MPU error status wile not mpu_err_trans_valid")

  // MPU FSM and bus interface should never assert trans valid at the same time
  a_mpu_bus_mpu_err_valid :
    assert property (@(posedge clk)
                     (! (bus_resp_valid_i && mpu_err_trans_valid) ))
      else `uvm_error("mpu", "MPU FSM and bus interface response collision")

  // Should only block core side upon when waiting for MPU error response
  a_mpu_block_core_iff_wait :
    assert property (@(posedge clk)
                     (mpu_block_core) |-> (state_q != MPU_IDLE) )
      else `uvm_error("mpu", "MPU blocking core side when not needed")

  // Should only block OBI side upon MPU error
  a_mpu_block_bus_iff_err :
    assert property (@(posedge clk)
                     (mpu_block_bus) |-> (mpu_err || (state_q != MPU_IDLE)) )
      else `uvm_error("mpu", "MPU blocking OBI side when not needed")

endmodule : cv32e40x_mpu_sva

