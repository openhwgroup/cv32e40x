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
// Description:    PMA (Physical Memory Attribution)                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_pma import cv32e40x_pkg::*;
  #(parameter bit          IF_STAGE = 1,
    parameter int unsigned PMA_NUM_REGIONS = 1,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{PMA_R_DEFAULT})
  (
   input logic [31:0] trans_addr_i,
   input logic        speculative_access_i,
   input logic        atomic_access_i,
   output logic       pma_err_o,
   output logic       pma_block_o,
   output logic       pma_bufferable_o,
   output logic       pma_cacheable_o
   );
  
  parameter PMA_ADDR_LSB = 0; // TODO:OE experiment and see if this makes a difference
  
  pma_region_t pma_cfg;
  logic [31:0] word_addr;

  // PMA addresses are word addresses
  assign word_addr =  {2'b00, trans_addr_i[31:2]};

  // Identify PMA region
  // TODO:OE make sure that priority is correct here (lowest index -> highest priority)
  always_comb begin

    // If no match, use default PMA config
    pma_cfg = PMA_R_DEFAULT;

    for(int i = PMA_NUM_REGIONS-1; i >= 0; i--)  begin
    //foreach (PMA_CFG[i]) begin. TODO:OE foreach starts on index 0. possible to go in the opposite direction?
      if((word_addr[31:PMA_ADDR_LSB] >= PMA_CFG[i].word_addr_low[31:PMA_ADDR_LSB]) && 
         (word_addr[31:PMA_ADDR_LSB] <  PMA_CFG[i].word_addr_high[31:PMA_ADDR_LSB])) begin
        pma_cfg = PMA_CFG[i];
      end
    end
  end

  
  // TODO:OE remove
  // Main memory:
  //             1. Idempotent (allow speculatove acces)
  //             2. Code execution is allowed
  // I/O:
  //             1. Not idempotent (speculative access not allowed)
  //             2. Code execution not allowed
  
  // Check transaction based on PMA region config
  always_comb begin

    pma_block_o      = 1'b0;
    pma_err_o        = 1'b0;

    // Check for atomic access
    if (atomic_access_i && !pma_cfg.atomic) begin
      pma_err_o = 1'b1;
      //pma_block_o = 1'b1; TODO:OE should this also be blocked..? I guess
    end

    // IF stage is only allowed to fetch from main memory (code execution only allowed from main memory)
    if (IF_STAGE && !pma_cfg.main) begin
      pma_err_o   = 1'b1;
      pma_block_o = 1'b1;
    end

    // Speculative access only allowed in main memory
    if (speculative_access_i && !pma_cfg.main) begin
      pma_err_o   = 1'b1;
      pma_block_o = 1'b1;
    end
    
  end

  // Set cacheable and bufferable based on PMA region attributes
  assign pma_bufferable_o = pma_cfg.bufferable;
  assign pma_cacheable_o  = pma_cfg.cacheable;


  // TODO:OE add assertions checking e.g. that main_mem supports atomic, and any other constraints in the spec
  // TODO:OE assert that 2 LSB's in address are alwyas 0.
  // TODO:OE assert that PMA_NUM_REGIONS = $size(PMA_CFG)
  // TODO:OE assert no misaligned accesses. What's really the definition of misaligned access? prefetcher/aligner and load-store unit splits misaligned transfers  
  
endmodule
