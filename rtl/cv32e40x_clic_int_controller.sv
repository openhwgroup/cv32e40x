// Copyright 2022 Silicon Labs, Inc.
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
// Engineers       Oystein Knauserud -     oystein.knauserud@silabs.com       //
//                                                                            //
// Design Name:    CLIC int controller                                        //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Controller for handling CLIC interrupts                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_clic_int_controller import cv32e40x_pkg::*;
#(
    parameter int SMCLIC_ID_WIDTH = 5
)
(
  input  logic                       clk,
  input  logic                       rst_n,

  // CLIC interface
  input  logic                       clic_irq_i,       // CLIC interrupt pending
  input  logic [SMCLIC_ID_WIDTH-1:0] clic_irq_id_i,    // ID of pending interrupt
  input  logic [7:0]                 clic_irq_level_i, // Level of pending interrupt
  input  logic [1:0]                 clic_irq_priv_i,  // Privilege level of pending interrupt
  input  logic                       clic_irq_shv_i,   // Is pending interrupt vectored?


  // To cv32e40x_controller
  output logic                       irq_req_ctrl_o,
  output logic [SMCLIC_ID_WIDTH-1:0] irq_id_ctrl_o,
  output logic                       irq_wu_ctrl_o,
  output logic                       irq_clic_shv_o,

  // To/from cv32e40x_cs_registers
  input  logic                       m_ie_i             // Interrupt enable bit from CSR (M mode)
);

  logic                       global_irq_enable;

  // Flops for breaking timing path to instruction interface
  logic                       clic_irq_q;
  logic [SMCLIC_ID_WIDTH-1:0] clic_irq_id_q;
  logic [7:0]                 clic_irq_level_q;
  logic [1:0]                 clic_irq_priv_q;
  logic                       clic_irq_shv_q;

  // Register interrupt input (on gated clock). The wake-up logic will
  // observe clic_irq_i as well, but in all other places clic_irq_q will be used to
  // avoid timing paths from clic_irq_i to instr_*_o

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      clic_irq_q  <= 1'b0;
    end else begin
      clic_irq_q  <= clic_irq_i;
    end
  end


  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      clic_irq_id_q     <= '0;
      clic_irq_level_q  <= '0;
      clic_irq_priv_q   <= PRIV_LVL_M;
      clic_irq_shv_q    <= 1'b0;
    end else begin
      if (clic_irq_i) begin
        clic_irq_id_q    <= clic_irq_id_i;
        clic_irq_level_q <= clic_irq_level_i;
        clic_irq_priv_q  <= clic_irq_priv_i;
        clic_irq_shv_q   <= clic_irq_shv_i;
      end
    end
  end

    // Global interrupt enable
  assign global_irq_enable = m_ie_i;

  ///////////////////////////
  // Outputs to controller //
  ///////////////////////////

  // Request to take interrupt if there a pending-and-enabled interrupt and interrupts are enabled globally
  // todo: factor in interrupt level and thresholds
  assign irq_req_ctrl_o = clic_irq_q && global_irq_enable;

  // Pass on interrupt ID
  assign irq_id_ctrl_o = clic_irq_id_q;

  // Wake-up signal based on unregistered IRQ such that wake-up can be caused if no clock is present
  assign irq_wu_ctrl_o = clic_irq_i;

  assign irq_clic_shv_o = clic_irq_shv_q;

endmodule // cv32e40x_clic_int_controller
