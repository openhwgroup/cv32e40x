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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Robert Balas - balasr@iis.ee.ethz.ch                       //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40x_controller_bypass                                 //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bypass logic, hazard detection and stall control           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_controller_bypass import cv32e40x_pkg::*;
  (
    // From controller_fsm
    input  logic        is_decoding_i,              // Core is in decoding state (from FSM)
  
    // From decoder
    input  logic [1:0]  ctrl_transfer_insn_raw_i,          // decoded control transfer instruction. Not gated with deassert
    input  logic [REGFILE_NUM_READ_PORTS-1:0]     rf_re_i, // Read enables from decoder
    input rf_addr_t  rf_raddr_i[REGFILE_NUM_READ_PORTS],   // Read addresses from decoder
    input rf_addr_t  rf_waddr_i,                           // Write address from decoder

    // From id_stage
    input  logic        regfile_alu_we_id_i,        // RF we in ID is due to an ALU ins, not LSU
  
    // From EX
    input  logic        rf_we_ex_i,                 // Register file write enable from EX stage
    input rf_addr_t     rf_waddr_ex_i,              // write address currently in EX
    input  logic        data_req_ex_i,              // data memory access is currently performed in EX stage
    
    // From WB
    input  logic        rf_we_wb_i,                 // Register file write enable from WB stage
    input rf_addr_t     rf_waddr_wb_i,              // write address currently in WB
    input  logic        wb_ready_i,                 // WB stage is ready
    input  logic        data_req_wb_i,              // LSU data is written back in WB

    // From LSU
    input  logic        data_misaligned_i,          // LSU detected a misaligned load/store instruction
  
    // forwarding mux sel outputs
    output op_fw_mux_e    operand_a_fw_mux_sel_o,   // operand_a forward mux sel
    output op_fw_mux_e    operand_b_fw_mux_sel_o,   // operand_b forward mux sel
    output jalr_fw_mux_e  jalr_fw_mux_sel_o,        // jump target forward mux sel

    // Stall outputs  
    output logic        misaligned_stall_o,         // Stall due to misaligned load/store
    output logic        jr_stall_o,                 // Stall due to JR hazard (JR used result from EX or LSU result in WB)
    output logic        load_stall_o,               // Stall due to load operation

    // To decoder
    output logic        deassert_we_o               // deassert write enable for next instruction
  
  );


  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_hz;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_hz;

  logic                              rf_wr_ex_match;
  logic                              rf_wr_wb_match;
  logic                              rf_wr_ex_hz;
  logic                              rf_wr_wb_hz;

  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////

  genvar i;
  generate
    for(i=0; i<REGFILE_NUM_READ_PORTS; i++) begin : gen_forward_signals
      // Does register file read address match write address in EX (excluding R0)?
      assign rf_rd_ex_match[i] = (rf_waddr_ex_i == rf_raddr_i[i]) && |rf_raddr_i[i] && rf_re_i[i];

      // Does register file read address match write address in WB (excluding R0)?
      assign rf_rd_wb_match[i] = (rf_waddr_wb_i == rf_raddr_i[i]) && |rf_raddr_i[i] && rf_re_i[i];

      // Load-read hazard (for any instruction following a load)
      assign rf_rd_ex_hz[i] = rf_rd_ex_match[i];
      assign rf_rd_wb_hz[i] = rf_rd_wb_match[i];
    end
  endgenerate

  // Does register file write address match write address in EX?
  assign rf_wr_ex_match = (rf_waddr_ex_i == rf_waddr_i);

  // Does register file write address match write address in WB?
  assign rf_wr_wb_match = (rf_waddr_wb_i == rf_waddr_i);

  // Load-write hazard (for non-load instruction following a load)
  // TODO:OK: Shouldn't bee needed as we now have a single write port
  assign rf_wr_ex_hz = rf_wr_ex_match && regfile_alu_we_id_i;
  assign rf_wr_wb_hz = rf_wr_wb_match && regfile_alu_we_id_i;

  always_comb
  begin
    load_stall_o   = 1'b0;
    deassert_we_o  = 1'b0;

    // deassert WE when the core is not decoding instructions
    if (~is_decoding_i)
      deassert_we_o = 1'b1;

    // Stall because of load operation
    if (
        (data_req_ex_i && rf_we_ex_i && |rf_rd_ex_hz) || // load-use hazard (EX)
        (!wb_ready_i   && rf_we_wb_i && |rf_rd_wb_hz) || // load-use hazard (WB during wait-state)
        (data_req_ex_i && rf_we_ex_i && is_decoding_i && !data_misaligned_i && rf_wr_ex_hz) ||  // TODO: remove?
        (!wb_ready_i   && rf_we_wb_i && is_decoding_i && !data_misaligned_i && rf_wr_wb_hz)     // TODO: remove? Probably SEC fail
       )
    begin
      deassert_we_o   = 1'b1;
      load_stall_o    = 1'b1;
    end

    // Stall because of jr path
    // - Stall if a result is to be forwarded to the PC
    // except if result from WB is an ALU result
    // we don't care about in which state the ctrl_fsm is as we deassert_we
    // anyway when we are not in DECODE
    if ((ctrl_transfer_insn_raw_i == BRANCH_JALR) &&
        ((rf_we_wb_i && rf_rd_wb_match[0] && data_req_wb_i) ||
         (rf_we_ex_i && rf_rd_ex_match[0])))
    begin
      jr_stall_o      = 1'b1;
      deassert_we_o   = 1'b1;
    end
    else
    begin
      jr_stall_o     = 1'b0;
    end
  end

  // stall because of misaligned data access
  assign misaligned_stall_o = data_misaligned_i;

  // Forwarding control unit
  always_comb
  begin
    // default assignements
    operand_a_fw_mux_sel_o = SEL_REGFILE;
    operand_b_fw_mux_sel_o = SEL_REGFILE;
    jalr_fw_mux_sel_o      = SELJ_REGFILE;

    // Forwarding WB -> ID
    if (rf_we_wb_i)
    begin
      if (rf_rd_wb_match[0])
        operand_a_fw_mux_sel_o = SEL_FW_WB;
      if ( rf_rd_wb_match[1])
        operand_b_fw_mux_sel_o = SEL_FW_WB;
    end

    // Forwarding EX -> ID (not actually used when there is a load in EX)
    if (rf_we_ex_i)
    begin
     if (rf_rd_ex_match[0])
       operand_a_fw_mux_sel_o = SEL_FW_EX;
     if (rf_rd_ex_match[1])
       operand_b_fw_mux_sel_o = SEL_FW_EX;
    end

    // Forwarding WB->ID for the jump register path
    // Only allowed if WB is writing back an ALU result; no forwarding for load result because of timing reasons
    if (rf_we_wb_i) begin
      if (rf_rd_wb_match[0] && !data_req_wb_i) begin
        jalr_fw_mux_sel_o = SELJ_FW_WB;
      end
    end

    // for misaligned memory accesses
    if (data_misaligned_i)
    begin
      operand_a_fw_mux_sel_o  = SEL_FW_EX;
      operand_b_fw_mux_sel_o  = SEL_REGFILE;
    end
  end

endmodule // cv32e40x_controller_bypass