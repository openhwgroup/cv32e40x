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
  #(  parameter bit          IF_STAGE                     = 1,
      parameter bit          A_EXTENSION                  = 0,
      parameter type         CORE_REQ_TYPE                = obi_inst_req_t,
      parameter type         CORE_RESP_TYPE               = inst_resp_t,
      parameter type         BUS_RESP_TYPE                = obi_inst_resp_t,
      parameter int          PMA_NUM_REGIONS              = 0,
      parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT})
  (
   input logic  clk,
   input logic  rst_n,

   input logic  atomic_access_i, // Indicate that ongoing access is atomic

   // Interface towards bus interface
   input logic  bus_trans_ready_i,
   output logic bus_trans_valid_o,
   output       CORE_REQ_TYPE bus_trans_o,

   input logic  bus_resp_valid_i,
   input        BUS_RESP_TYPE bus_resp_i,

   // Interface towards core
   input logic  core_trans_valid_i,
   output logic core_trans_ready_o,
   input        CORE_REQ_TYPE core_trans_i,

   output logic core_resp_valid_o,
   output       CORE_RESP_TYPE core_resp_o,
   
   // Indication from the core that there will be one pending transaction in the next cycle
   input logic  core_one_txn_pend_n
   );

  logic        pma_err;
  logic        mpu_err;
  logic        mpu_block_core;
  logic        mpu_block_bus;
  logic        mpu_err_trans_valid;
  logic        mpu_err_trans_ready;
  mpu_status_e mpu_status;
  mpu_state_e  state_q, state_n;
  logic        bus_trans_cacheable;
  logic        bus_trans_bufferable;
  logic        core_trans_we;
  logic        execute_access;
  logic        speculative_access;
  
  // FSM that will "consume" transfers failing PMA checks.
  // Upon failing checks, this FSM will prevent the transfer from going out on the bus
  // and wait for all in flight bus transactions to complete while blocking new transfers.
  // When all in flight transactions are complete, it will respond with the correct status before
  // allowing new transfers to go through.
  // The input signal core_one_txn_pend_n indicates that there, from the core's point of view,
  // will be one pending transaction in the next cycle. Upon MPU error, this transaction
  // will be completed by this FSM
  always_comb begin

    state_n             = state_q;
    mpu_status          = MPU_OK;
    mpu_block_core      = 1'b0;
    mpu_block_bus       = 1'b0;
    mpu_err_trans_valid = 1'b0;
    mpu_err_trans_ready = 1'b0;

    case(state_q)
      MPU_IDLE: begin
        if (mpu_err && core_trans_valid_i) begin

          // Block transfer from going out on the bus.
          mpu_block_bus  = 1'b1;

          // Signal to the core that the transfer was accepted (but will be consumed by the MPU)
          mpu_err_trans_ready = 1'b1;

          if(core_trans_we) begin
            // MPU error on write
            state_n = core_one_txn_pend_n ? MPU_WR_ERR_RESP : MPU_WR_ERR_WAIT;
          end
          else begin
            // MPU error on read
            state_n = core_one_txn_pend_n ? MPU_RE_ERR_RESP : MPU_RE_ERR_WAIT;
          end

        end
      end
      MPU_RE_ERR_WAIT, MPU_WR_ERR_WAIT: begin

        // Block new transfers while waiting for in flight transfers to complete
        mpu_block_bus  = 1'b1;
        mpu_block_core = 1'b1;

        if (core_one_txn_pend_n) begin
          state_n = (state_q == MPU_RE_ERR_WAIT) ? MPU_RE_ERR_RESP : MPU_WR_ERR_RESP;
        end
      end
      MPU_RE_ERR_RESP, MPU_WR_ERR_RESP: begin

        // Keep blocking new transfers
        mpu_block_bus  = 1'b1;
        mpu_block_core = 1'b1;

        // Set up MPU error response towards the core
        mpu_err_trans_valid = 1'b1;
        mpu_status = (state_q == MPU_RE_ERR_RESP) ? MPU_RE_FAULT : MPU_WR_FAULT;

        // Go back to IDLE uncoditionally. 
        // The core is expected to always be ready for the response
        state_n = MPU_IDLE;

      end
      default: ;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      state_q     <= MPU_IDLE;
    end
    else begin
      state_q <= state_n;
    end
  end

  // Forward transaction request towards bus interface
  assign bus_trans_valid_o = core_trans_valid_i && !mpu_block_bus;

  always_comb begin
    bus_trans_o            = core_trans_i;
    bus_trans_o.memtype[0] = bus_trans_bufferable;
    bus_trans_o.memtype[1] = bus_trans_cacheable;
  end

  // Forward transaction response towards core
  assign core_resp_valid_o      = bus_resp_valid_i || mpu_err_trans_valid;
  assign core_resp_o.bus_resp   = bus_resp_i;
  assign core_resp_o.mpu_status = mpu_status;

  // Signal ready towards core
  assign core_trans_ready_o     = (bus_trans_ready_i && !mpu_block_core) || mpu_err_trans_ready;

  // PMA - Physical Memory Attribution
  cv32e40x_pma
    #(.A_EXTENSION(A_EXTENSION),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  pma_i
    (.trans_addr_i(core_trans_i.addr),
     .speculative_access_i(speculative_access),
     .atomic_access_i(atomic_access_i),
     .execute_access_i(execute_access),
     .pma_err_o(pma_err),
     .pma_bufferable_o(bus_trans_bufferable),
     .pma_cacheable_o(bus_trans_cacheable));
  

  assign mpu_err = pma_err;

  // Writes are only supported on the data interface
  // Tie to 1'b0 if this MPU is instantiatied in the IF stage
  generate
    if (IF_STAGE) begin: mpu_if
      assign core_trans_we      = 1'b0;
      assign execute_access     = 1'b1;
      assign speculative_access = 1'b1;
    end
    else begin: mpu_lsu
      assign core_trans_we      = core_trans_i.we;
      assign execute_access     = 1'b0;
      assign speculative_access = 1'b0;
    end
  endgenerate

endmodule
