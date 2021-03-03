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
// Description:    MPU (Memory Protection Unit)                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_mpu import cv32e40x_pkg::*;
  #(parameter bit          IF_STAGE = 1,
    parameter int unsigned PMA_NUM_REGIONS = 1,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{PMA_R_DEFAULT})
  (

   input logic                       speculative_access_i,
   input logic                       atomic_access_i,

   // Interface towards bus interface
   input logic                       obi_if_trans_ready_i,
   output logic [31:0]               obi_if_trans_addr_o,
   output logic                      obi_if_trans_valid_o,
   input logic                       obi_if_resp_valid_i,
   input obi_inst_resp_t             obi_if_resp,

   // Interface towards prefetcher
   input logic [31:0]                prefetch_trans_addr_i,
   input logic                       prefetch_trans_valid_i,
   output logic                      prefetch_trans_ready_o,
   output logic                      prefetch_resp_valid_o,
   output inst_resp_t                prefetch_inst_resp_o
   );

  // TODO:OE add obi prot
  
  logic        pma_err;
  logic        pma_bufferable_o;
  logic        pma_cacheable_o;
  logic        pmp_block;
  logic        pma_block;
  logic        mpu_block;
  mpu_status_e mpu_status;

  
  assign pmp_block = 1'b0; // TODO: connect to PMP
  assign mpu_block = pma_block || pmp_block;

  // Signals towards OBI interface
  assign obi_if_trans_addr_o    = prefetch_trans_addr_i;
  assign obi_if_trans_valid_o   = prefetch_trans_valid_i && !mpu_block;

  // Signals towards prefetcher
  assign prefetch_trans_ready_o = obi_if_trans_ready_i || mpu_block;
  assign prefetch_resp_valid_o  = obi_if_resp_valid_i;

  assign prefetch_inst_resp_o.bus_resp        = obi_if_resp;
  assign prefetch_inst_resp_o.mpu_status      = mpu_status;
  
  // PMA - Physical Memory Attribution
  cv32e40x_pma 
    #(.IF_STAGE(IF_STAGE),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  pma_i
    (.trans_addr_i(prefetch_trans_addr_i),
     .speculative_access_i(speculative_access_i),
     .atomic_access_i(atomic_access_i),
     .pma_err_o(pma_err),
     .pma_block_o(pma_block),
     .pma_bufferable_o(pma_bufferable_o),
     .pma_cacheable_o(pma_cacheable_o));

  // TODO:OE clean
  always_comb begin
    
    mpu_status = MPU_OK;

    if (pma_err && IF_STAGE) begin
      mpu_status = MPU_INSTR_ACCESS_FAULT;
    end

    if(pma_err && !IF_STAGE && 0 /*trans_we*/) begin
      mpu_status = MPU_STORE_ACCESS_FAULT;
    end

    if(pma_err && !IF_STAGE && 0 /*!trans_we*/) begin
      mpu_status = MPU_LOAD_ACCESS_FAULT;
    end
  end

  // TODO assert: mpu_block -> mpu_status != MPU_OK
 
endmodule
