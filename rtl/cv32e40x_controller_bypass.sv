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
#(
  parameter int unsigned REGFILE_NUM_READ_PORTS = 2,
  parameter a_ext_e      A_EXT                  = A_NONE
)
(
  // From decoder
  input  logic [REGFILE_NUM_READ_PORTS-1:0]     rf_re_id_i, // Read enables from decoder
  input rf_addr_t     rf_raddr_id_i[REGFILE_NUM_READ_PORTS],// Read addresses from decoder

  // Pipeline registers
  input if_id_pipe_t  if_id_pipe_i,
  input id_ex_pipe_t  id_ex_pipe_i,
  input ex_wb_pipe_t  ex_wb_pipe_i,

  // From ID
  input  logic        alu_jmpr_id_i,              // ALU jump register (JALR)
  input  logic        sys_mret_id_i,              // mret in ID
  input  logic        csr_en_raw_id_i,            // CSR in ID (not gated with deassert)

  // From EX
  input  logic        csr_counter_read_i,         // CSR is reading a counter (EX).
  input  logic        csr_mnxti_read_i,           // CSR is reading mnxti (EX)

  // From WB
  input  logic        wb_ready_i,                 // WB stage is ready
  input  logic        csr_irq_enable_write_i,     // WB is writing to a CSR that may enable an interrupt.

  // From LSU
  input  lsu_atomic_e lsu_atomic_ex_i,
  input  lsu_atomic_e lsu_atomic_wb_i,
  input  logic        lsu_bus_busy_i,

  // From CS registers
  input  csr_hz_t     csr_hz_i,

  // Controller Bypass outputs
  output ctrl_byp_t   ctrl_byp_o
);

  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_match;            // Register file address match (ID vs. EX). Not qualified with rf_we_ex yet.
  logic                              rf_rd_ex_jalr_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_match;            // Register file address match (ID vs. WB). Not qualified with rf_we_wb yet.
  logic                              rf_rd_wb_jalr_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_hz;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_hz;

  logic                              csr_write_in_ex_wb;        // Detect CSR write in EX or WB (implicit and explicit)
  logic                              csr_write_in_ex;           // Detect CSR write in EX (implicit and explicit)
  logic                              csr_write_in_wb;           // Detect CSR write in WB (implicit and explicit)
  logic                              csr_impl_write_in_ex;      // Detect implicit CSR write in EX
  logic                              csr_impl_write_in_wb;      // Detect implicit CSR write in WB
  logic                              csr_expl_hz_ex;            // Explicit CSR hazard in EX

  logic                              rf_we_ex;                  // EX register file write enable
  logic                              rf_we_wb;                  // WB register file write enable
  logic                              lsu_en_wb;                 // WB lsu_en

  rf_addr_t                          rf_waddr_ex;               // EX rf_waddr
  rf_addr_t                          rf_waddr_wb;               // WB rf_waddr

  logic                              sys_mret_unqual_id;        // MRET in ID (not qualified with sys_en)
  logic                              csr_impl_rd_unqual_id;     // Implicit CSR read in ID (not qualified)
  logic                              jmpr_unqual_id;            // JALR in ID (not qualified with alu_en)
  logic                              tbljmp_unqual_id;          // Table jump in ID (not qualified with alu_en)

  assign rf_we_ex = id_ex_pipe_i.rf_we && id_ex_pipe_i.instr_valid;
  assign rf_we_wb = ex_wb_pipe_i.rf_we && ex_wb_pipe_i.instr_valid;
  assign lsu_en_wb = ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid;

  assign rf_waddr_ex = id_ex_pipe_i.rf_waddr;
  assign rf_waddr_wb = ex_wb_pipe_i.rf_waddr; // TODO:XIF If XIF OoO is allowed, we need to look at WB stage outputs instead

  // The following unqualified signals are such that they can have a false positive (but no false negative).
  //
  // There are two reasons why these signals are considered unqualified:
  // - The corresponding _en signal is not used
  // - A raw _en signal is used (i.e. deassert_we is ignored)
  //
  // This can lead to stall cycles (via jalr_stall or csr_stall) when they should not actually be needed.
  // Such cases are however rare as the difference between qualified and unqualified signals will only
  // occur in case that deassert_we = 1. Permanent stalls are avoided because the EX, WB stages will
  // eventually empty out removing that reasons for stall conditions.

  assign sys_mret_unqual_id = sys_mret_id_i && if_id_pipe_i.instr_valid;
  assign jmpr_unqual_id = alu_jmpr_id_i && if_id_pipe_i.instr_valid;
  assign tbljmp_unqual_id = if_id_pipe_i.instr_meta.tbljmp && if_id_pipe_i.instr_valid;

  // Any implicit CSR reads from the ID stage
  // mret reads mepc and mcause
  // tablejumps read jvt
  assign csr_impl_rd_unqual_id = sys_mret_unqual_id || tbljmp_unqual_id;

  // Detect any implicit CSR write currently in in EX (actual write will happen in WB)
  // mret, dret and CLIC/mret pointers implicitly writes to CSRs. (dret is killing IF/ID/EX once it is in WB and can be disregarded here.
  // Some CSR instructions perform writes to other CSRs, encoded by 'ex_wb_pipe_i.csr_impl_wr'
  assign csr_impl_write_in_ex = (id_ex_pipe_i.instr_valid &&
                                 (((id_ex_pipe_i.sys_en && id_ex_pipe_i.sys_mret_insn) || id_ex_pipe_i.instr_meta.clic_ptr || id_ex_pipe_i.instr_meta.mret_ptr) ||
                                  (id_ex_pipe_i.csr_en && csr_hz_i.impl_wr_ex)));

  // Detect any implicit CSR write in WB
  // mret, dret and CLIC/mret pointers implicitly writes to CSRs. (dret is killing IF/ID/EX once it is in WB and can be disregarded here.
  // Some CSR instructions perform writes to other CSRs, encoded by 'ex_wb_pipe_i.csr_impl_wr'
  assign csr_impl_write_in_wb = (ex_wb_pipe_i.instr_valid &&
                                 (((ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_mret_insn) || ex_wb_pipe_i.instr_meta.clic_ptr || ex_wb_pipe_i.instr_meta.mret_ptr) ||
                                  (ex_wb_pipe_i.csr_en && ex_wb_pipe_i.csr_impl_wr)));

  // Detect implicit and explicit CSR writes in EX
  assign csr_write_in_ex = id_ex_pipe_i.instr_valid && (id_ex_pipe_i.csr_en || csr_impl_write_in_ex);

  // Detect implicit and explicit CSR writes in WB
  assign csr_write_in_wb = ex_wb_pipe_i.instr_valid && (ex_wb_pipe_i.csr_en || csr_impl_write_in_wb);

  // Any CSR access (implicit or explicit) in any of EX and WB stages
  assign csr_write_in_ex_wb = csr_write_in_ex || csr_write_in_wb;

  // Detect RAW hazard for explicit CSR accesses in EX vs WB
  assign csr_expl_hz_ex = (csr_hz_i.expl_re_ex && csr_hz_i.expl_we_wb) &&
                          (csr_hz_i.expl_raddr_ex == csr_hz_i.expl_waddr_wb);

  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////

  // Stall ID when instruction that can trigger sleep (e.g. WFI or WFE) is active in EX.
  // Prevent load/store following a sleep instruction in the pipeline
  assign ctrl_byp_o.sleep_stall = (id_ex_pipe_i.sys_en && (id_ex_pipe_i.sys_wfi_insn || id_ex_pipe_i.sys_wfe_insn) && id_ex_pipe_i.instr_valid);

  // Stall ID when mnxti CSR is accessed in EX
  // This is needed because the data bypass from EX uses csr_rdata, and for mnxti this is actually mstatus and not the result
  // that will be written to the register file. Could be optimized to only stall when the result from the CSR instruction is used in ID,
  // but the common usecase is a CSR access followed by a branch using the mnxti result in the RF, so it would likely stall in most cases anyway.
  assign ctrl_byp_o.mnxti_id_stall = csr_mnxti_read_i;

  // Stall EX stage when an mnxti is in EX and an LSU instruction is in WB.
  // This is needed to make sure that any external interrupt clearing (due to a LSU instruction) gets picked
  // up correctly by the mnxti access.
  assign ctrl_byp_o.mnxti_ex_stall = csr_mnxti_read_i && (ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid);

  genvar i;
  generate
    for(i=0; i<REGFILE_NUM_READ_PORTS; i++) begin : gen_forward_signals
      // Does register file read address match write address in EX (excluding R0)?
      assign rf_rd_ex_match[i] = (rf_waddr_ex == rf_raddr_id_i[i]) && |rf_raddr_id_i[i] && rf_re_id_i[i];

      // Does register file read address match write address in WB (excluding R0)?
      assign rf_rd_wb_match[i] = (rf_waddr_wb == rf_raddr_id_i[i]) && |rf_raddr_id_i[i] && rf_re_id_i[i];

      // Load-read hazard (for any instruction following a load)
      assign rf_rd_ex_hz[i] = rf_rd_ex_match[i];
      assign rf_rd_wb_hz[i] = rf_rd_wb_match[i];
    end
  endgenerate

  // JALR rs1 match (rf_re_id_i[0] implied by JALR).
  // Not qualified yet with JALR instruction nor with read enable (implied by JALR)
  assign rf_rd_ex_jalr_match = (rf_waddr_ex == rf_raddr_id_i[0]) && |rf_raddr_id_i[0];
  assign rf_rd_wb_jalr_match = (rf_waddr_wb == rf_raddr_id_i[0]) && |rf_raddr_id_i[0];

  always_comb
  begin
    ctrl_byp_o.load_stall          = 1'b0;
    ctrl_byp_o.deassert_we         = 1'b0;
    ctrl_byp_o.csr_stall_id        = 1'b0;
    ctrl_byp_o.csr_stall_ex        = 1'b0;
    ctrl_byp_o.minstret_stall      = 1'b0;
    ctrl_byp_o.irq_enable_stall    = 1'b0;

    // deassert WE when the core has an exception in ID (ins converted to nop and propagated to WB)
    // Also deassert for trigger match, as with dcsr.timing==0 we do not execute before entering debug mode
    // CLIC pointer fetches go through the pipeline, but no write enables should be active.
    if (if_id_pipe_i.instr.bus_resp.err || !(if_id_pipe_i.instr.mpu_status == MPU_OK) || (|if_id_pipe_i.trigger_match) ||
        if_id_pipe_i.instr_meta.clic_ptr || if_id_pipe_i.instr_meta.mret_ptr) begin
      ctrl_byp_o.deassert_we = 1'b1;
    end

    // Stall because of load or XIF operation
    if (
        ((id_ex_pipe_i.lsu_en || id_ex_pipe_i.xif_en) && rf_we_ex && |rf_rd_ex_hz) || // load-use hazard (EX)
        (!wb_ready_i                                  && rf_we_wb && |rf_rd_wb_hz)    // load-use hazard (WB during wait-state)
       )
    begin
      ctrl_byp_o.load_stall  = 1'b1;
    end

    // Stall because of jalr path. Stall if a result is to be forwarded to the PC except if result from WB is an ALU result.
    // No need to deassert anything in ID as ID stage is stalled anyway. JALR implies rf_re_id_i[0].
    // Also stalling when a CSR access to MNXTI is in WB. This is because the jalr forward uses the ex_wb_pipe.rf_wdata as data,
    // and forwarding the CSR result (pointer address for mnxti) would need the forward mux to also include the pointer address from cs_registers.
    // Cannot use wb_stage.rf_wdata_o due to the timing path from the data OBI.
    if (jmpr_unqual_id &&
         ((rf_we_wb && rf_rd_wb_jalr_match && lsu_en_wb) ||
          (rf_we_wb && rf_rd_wb_jalr_match && (ex_wb_pipe_i.csr_mnxti_access && ex_wb_pipe_i.csr_en)) ||
          (rf_we_ex && rf_rd_ex_jalr_match))) begin
      ctrl_byp_o.jalr_stall = 1'b1;
    end else begin
      ctrl_byp_o.jalr_stall = 1'b0;
    end

    ////////////////
    // CSR stalls //
    ////////////////

    // Implicit CSR read in ID: Conservatively stall on any implicit CSR write in EX or WB
    // Implicit CSR read in ID: Conservatively stall on any explicit CSR write in EX or WB
    // Implicit CSR read in EX: Conservatively stall on any implicit CSR write in WB
    // Implicit CSR read in EX: Conservatively stall on any explicit CSR write in WB
    // Explicit CSR read in EX: Conservatively stall on any implicit CSR write in WB
    // Explicit CSR read in EX: Precise stall on any explicit CSR write in WB

    // Stall ID because of an implicit CSR read is in ID while CSR (implicit or explicit) is written in EX/WB
    // This stall is very conservative as it stalls on any CSR access in EX or WB.
    // mret reads mcause and mepc (via controller_fsm) in the ID stage
    // tablejumps read jvt in the ID stage
    if (csr_impl_rd_unqual_id && csr_write_in_ex_wb) begin
      ctrl_byp_o.csr_stall_id = 1'b1;
    end

    // Stall EX because of
    // 1: an implicit CSR read is being performed while an implicit or explicit CSR write is in WB,
    // 2: or an explicit CSR read is in EX while any implicit write is in WB (conservative stall)
    // 3: or an explicit CSR read is in EX while an explicit CSR write to the same CSR is in WB. (exact stall)
    //
    // Cases like accesses to mscratchcswl and mnxti which reads multiple CSRs are handled by 1 above.
    if ((csr_hz_i.impl_re_ex && csr_write_in_wb) ||
        (id_ex_pipe_i.csr_en && id_ex_pipe_i.instr_valid && csr_impl_write_in_wb) ||
        csr_expl_hz_ex) begin

      ctrl_byp_o.csr_stall_ex = 1'b1;
    end

    // Stall (EX) due to performance counter read
    // csr_counter_read_i is derived from csr_raddr, which is gated with id_ex_pipe.csr_en and id_ex_pipe.instr_valid
    if (csr_counter_read_i && ex_wb_pipe_i.instr_valid) begin
      ctrl_byp_o.minstret_stall = 1'b1;
    end

    // Stall EX when an interrupt may be enabled from WB while there is a LSU instruction in EX.
    if (csr_irq_enable_write_i && (id_ex_pipe_i.instr_valid && id_ex_pipe_i.lsu_en)) begin
      ctrl_byp_o.irq_enable_stall = 1'b1;
    end
  end

  generate
    if (A_EXT != A_NONE) begin : atomic_stall
      always_comb begin
        ctrl_byp_o.atomic_stall = 1'b0;

        // Stall EX for the following two scenarios
        // 1: There is an atomic instruction in EX while we have outstanding transactions on the bus
        // 2: There is any LSU instruction in EX while there is an outstanding atomic transfer in progress
        if ((id_ex_pipe_i.lsu_en && (lsu_atomic_ex_i != AT_NONE) && id_ex_pipe_i.instr_valid) ||
            (id_ex_pipe_i.lsu_en && id_ex_pipe_i.instr_valid && ex_wb_pipe_i.lsu_en && (lsu_atomic_wb_i != AT_NONE) && ex_wb_pipe_i.instr_valid)) begin
            ctrl_byp_o.atomic_stall = lsu_bus_busy_i;
        end
      end
    end else begin : no_atomic_stall
      assign ctrl_byp_o.atomic_stall = 1'b0;
    end
  endgenerate

  assign ctrl_byp_o.id_stage_abort = ctrl_byp_o.deassert_we;

  // Forwarding control unit
  always_comb
  begin
    // default assignements
    ctrl_byp_o.operand_a_fw_mux_sel = SEL_REGFILE;
    ctrl_byp_o.operand_b_fw_mux_sel = SEL_REGFILE;
    ctrl_byp_o.jalr_fw_mux_sel      = SELJ_REGFILE;

    // Forwarding WB -> ID
    if (rf_we_wb) begin
      if (rf_rd_wb_match[0]) begin
        ctrl_byp_o.operand_a_fw_mux_sel = SEL_FW_WB;
      end
      if (rf_rd_wb_match[1]) begin
        ctrl_byp_o.operand_b_fw_mux_sel = SEL_FW_WB;
      end
    end

    // Forwarding EX -> ID (not actually used when there is a load in EX)
    if (rf_we_ex) begin
      if (rf_rd_ex_match[0]) begin
        ctrl_byp_o.operand_a_fw_mux_sel = SEL_FW_EX;
      end
      if (rf_rd_ex_match[1]) begin
        ctrl_byp_o.operand_b_fw_mux_sel = SEL_FW_EX;
      end
    end

    // Forwarding WB->ID for the jump register path
    // Only used if WB is writing back an ALU result. No forwarding for load result because of timing reasons.
    // Non qualified rf_rd_wb_jalr_match is used as it is a don't care if jmpr_unqual_id = 0 or jalr_stall = 1.
    if (rf_we_wb) begin
      if (rf_rd_wb_jalr_match) begin
        ctrl_byp_o.jalr_fw_mux_sel = SELJ_FW_WB;
      end
    end
  end

  // Stall EX if offloaded instruction in WB may trigger an exception
  assign ctrl_byp_o.xif_exception_stall = ex_wb_pipe_i.xif_en && ex_wb_pipe_i.xif_meta.exception && ex_wb_pipe_i.instr_valid;

endmodule
