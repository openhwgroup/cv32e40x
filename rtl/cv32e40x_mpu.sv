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
    parameter type         RESP_TYPE = inst_resp_t, // TODO: use this to separate between instuction and data side
    parameter int unsigned MAX_IN_FLIGHT = 2,
    parameter int unsigned PMA_NUM_REGIONS = 1,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{PMA_R_DEFAULT})
  (
   input logic                clk,
   input logic                rst_n,
   
   input logic                speculative_access_i,
   input logic                atomic_access_i,

   // Interface towards bus interface
   input logic                obi_if_trans_ready_i,
   output logic [31:0]        obi_if_trans_addr_o,
   output logic               obi_if_trans_valid_o,
   input logic                obi_if_resp_valid_i,
   input obi_inst_resp_t      obi_if_resp_i,

   // Interface towards core
   input logic [31:0]         core_trans_addr_i,
   input logic                core_trans_we_i,
   input logic                core_trans_valid_i,
   output logic               core_trans_ready_o,
   output logic               core_resp_valid_o,
   output inst_resp_t         core_inst_resp_o
   );

  localparam IN_FLIGHT_WIDTH = $clog2(MAX_IN_FLIGHT+1); // +1 to include 0
  
  logic        pma_err;
  logic        pmp_err;
  logic        mpu_err;
  logic        pma_bufferable;
  logic        pma_cacheable;
  logic        mpu_block_core;
  logic        mpu_block_obi;
  logic        mpu_err_trans_valid;
  mpu_status_e mpu_status;
  mpu_state_e state_q, next_state;
  logic [IN_FLIGHT_WIDTH-1:0] in_flight_q, in_flight_n;
  
  
  always_comb begin

    next_state     = state_q;
    mpu_status     = MPU_OK;
    mpu_block_core = 1'b0;
    mpu_block_obi  = 1'b0;
    mpu_err_trans_valid = 1'b0;
    
    case(state_q)
      MPU_IDLE: begin
        if (mpu_err && core_trans_valid_i && obi_if_trans_ready_i) begin

          // Block transfer from going out on the bus.
          mpu_block_obi  = 1'b1;

          if(core_trans_we_i) begin
            // MPU error on write
            next_state = (in_flight_n == 0) ? MPU_WR_ERR_RESP : MPU_RE_ERR_WAIT;
          end
          else begin
            // MPU error on read
            next_state = (in_flight_n == 0) ? MPU_RE_ERR_RESP : MPU_WR_ERR_WAIT;
          end
        end
      end
      MPU_RE_ERR_WAIT, MPU_WR_ERR_WAIT: begin

        // Block new transfers while waiting for in flight transfers to complete
        mpu_block_obi  = 1'b1;
        mpu_block_core = 1'b1;
        
        if (in_flight_n == 0) begin
          next_state = (state_q == MPU_RE_ERR_WAIT) ? MPU_RE_ERR_RESP : MPU_WR_ERR_RESP;
        end
      end
      MPU_RE_ERR_RESP, MPU_WR_ERR_RESP: begin

        // These states mimic the response phase.
        // Set the MPU status for read/write errors
        // New transfers are allowed to pass through

        // Set up MPU error response towards the core
        mpu_err_trans_valid = 1'b1;
        mpu_status = (state_q == MPU_RE_ERR_RESP) ? MPU_RE_FAULT : MPU_WR_FAULT;
        
        // Check for MPU error on new transfer
        if (mpu_err && core_trans_valid_i && obi_if_trans_ready_i) begin

          // Block transfer from going out on the bus.
          mpu_block_obi  = 1'b1;
          
          if(core_trans_we_i) begin
            // MPU error on write
            next_state = (in_flight_n == 0) ? MPU_WR_ERR_RESP : MPU_RE_ERR_WAIT;
          end
          else begin
            // MPU error on read
            next_state = (in_flight_n == 0) ? MPU_RE_ERR_RESP : MPU_WR_ERR_WAIT;
          end
        end
        else begin
          // No new transfer, go back to idle
          next_state = MPU_IDLE;
        end
      end
      default: ;
    endcase
  end

  // Keep track of in-flight transactions
  always_comb begin
    in_flight_n = in_flight_q;
    
    if (obi_if_trans_valid_o && obi_if_trans_ready_i) begin
      if (!obi_if_resp_valid_i) begin
        in_flight_n = in_flight_q + IN_FLIGHT_WIDTH'(1);
      end
    end
    else if (obi_if_resp_valid_i) begin
      in_flight_n = in_flight_q - IN_FLIGHT_WIDTH'(1);
    end
  end
  
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      state_q     <= MPU_IDLE;
      in_flight_q <= '0;
    end
    else begin
      state_q <= next_state;
      in_flight_q <= in_flight_n;
    end
  end

  // Signals towards OBI interface (TODO:OE add remainig signals for data side, e.g. we)
  assign obi_if_trans_valid_o = core_trans_valid_i && !mpu_block_obi;
  assign obi_if_trans_addr_o  = core_trans_addr_i;
  
  // Signals towards core
  /*TODO:OE Blocking is not the same as in spec. core_trans_ready_o will only be supressed to block transfers when "consuming" a tranfer due to MPU error, we'll still wait for the downstream obi-if to be ready (but we won't pass the transfer on)*/
  assign core_trans_ready_o          = obi_if_trans_ready_i && !mpu_block_core; 
  assign core_resp_valid_o           = obi_if_resp_valid_i || mpu_err_trans_valid;
  assign core_inst_resp_o.bus_resp   = obi_if_resp_i;
  assign core_inst_resp_o.mpu_status = mpu_status;
  
  // PMA - Physical Memory Attribution
  cv32e40x_pma
    #(.IF_STAGE(IF_STAGE),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  pma_i
    (.trans_addr_i(core_trans_addr_i),
     .speculative_access_i(speculative_access_i),
     .atomic_access_i(atomic_access_i),
     .pma_err_o(pma_err),
     .pma_bufferable_o(pma_bufferable),
     .pma_cacheable_o(pma_cacheable));
  
  assign pmp_err = 1'b0; // TODO connect to PMP
  assign mpu_err = pmp_err || pma_err;
  
endmodule
