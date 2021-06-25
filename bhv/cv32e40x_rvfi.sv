// Copyright (c) 2020 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

// CV32E40X RVFI interface
// Contributors: Davide Schiavone <davide@openhwgroup.org>
//               Halfdan Bechmann <halfdan.bechmann@silabs.com>

module cv32e40x_rvfi
  import cv32e40x_pkg::*;
  import cv32e40x_rvfi_pkg::*;
  (
   input logic                                clk_i,
   input logic                                rst_ni,

   //// IF Probes ////
   input logic [31:0]                         pc_if_i,

   //// ID probes ////
   input logic [31:0]                         pc_id_i,
   input logic                                instr_id_valid_i,
   input logic [31:0]                         jump_target_id_i,
   // LSU
   input logic                                lsu_en_id_i,
   input logic                                lsu_we_id_i,
   input logic [1:0]                          lsu_type_id_i,
   // Register reads
   input logic [4:0]                          rs1_addr_id_i,
   input logic [31:0]                         rs1_rdata_id_i,
   input logic [4:0]                          rs2_addr_id_i,
   input logic [31:0]                         rs2_rdata_id_i,

   //// EX probes ////
   input logic                                insn_ebrk_ex_i,
   input logic                                insn_ecall_ex_i,
   input logic                                insn_fencei_ex_i,
   input logic                                insn_mret_ex_i,
   // LSU
   input logic                                lsu_en_ex_i,
   input logic                                illegal_insn_ex_i,

   input logic                                instr_ex_ready_i,
   input logic                                instr_ex_valid_i,

   input logic [31:0]                         branch_target_ex_i,

   input logic [31:0]                         lsu_addr_ex_i,
   input logic [31:0]                         lsu_wdata_ex_i,
   input logic                                lsu_misaligned_ex_i,

   //// WB probes ////
   input logic [31:0]                         pc_wb_i,
   input logic                                wb_ready_i,
   input logic                                wb_valid_i,
   input logic [31:0]                         instr_rdata_wb_i,
   input logic                                insn_ebrk_wb_i,
   input logic                                insn_ecall_wb_i,
   input logic                                insn_fencei_wb_i,
   input logic                                insn_mret_wb_i,
   input logic                                illegal_insn_wb_i,
   // Register writes
   input logic                                rd_we_wb_i,
   input logic [4:0]                          rd_addr_wb_i,
   input logic [31:0]                         rd_wdata_wb_i,
   // LSU
   input logic                                lsu_en_wb_i,
   input logic                                lsu_rvalid_wb_i,
   input logic [31:0]                         lsu_rdata_wb_i,
   // PC //
   input logic                                pc_set_i,
   input                                      pc_mux_e pc_mux_i,
   input                                      exc_pc_mux_e exc_pc_mux_i,
   input logic [31:0]                         exception_target_wb_i,
   input logic [31:0]                         mepc_target_wb_i,

   //// CSR Probes ////
   input                                      Status_t csr_mstatus_n_i,
   input                                      Status_t csr_mstatus_q_i,
   input logic                                csr_mstatus_we_i,
   input logic [31:0]                         csr_misa_n_i,
   input logic [31:0]                         csr_misa_q_i,
   input logic                                csr_misa_we_i,
   input logic [31:0]                         csr_mie_n_i,
   input logic [31:0]                         csr_mie_q_i,
   input logic                                csr_mie_we_i,
   input                                      Mtvec_t csr_mtvec_n_i,
   input                                      Mtvec_t csr_mtvec_q_i,
   input logic                                csr_mtvec_we_i,
   input logic [31:0]                         csr_mcountinhibit_n_i,
   input logic [31:0]                         csr_mcountinhibit_q_i,
   input logic                                csr_mcountinhibit_we_i,
   input logic [31:0] [31:0]                  csr_mhpmevent_n_i,
   input logic [31:0] [31:0]                  csr_mhpmevent_q_i,
   input logic                                csr_mhpmevent_we_i,
   input logic [31:0]                         csr_mscratch_n_i,
   input logic [31:0]                         csr_mscratch_q_i,
   input logic                                csr_mscratch_we_i,
   input logic [31:0]                         csr_mepc_n_i,
   input logic [31:0]                         csr_mepc_q_i,
   input logic                                csr_mepc_we_i,
   input                                      Mcause_t csr_mcause_n_i,
   input                                      Mcause_t csr_mcause_q_i,
   input logic                                csr_mcause_we_i,
   input logic [31:0]                         csr_mip_n_i,
   input logic [31:0]                         csr_mip_q_i,
   input logic                                csr_mip_we_i,
   input logic [31:0]                         csr_tdata1_n_i,
   input logic [31:0]                         csr_tdata1_q_i,
   input logic                                csr_tdata1_we_i,
   input logic [31:0]                         csr_tdata2_n_i,
   input logic [31:0]                         csr_tdata2_q_i,
   input logic                                csr_tdata2_we_i,
   input logic [31:0]                         csr_tinfo_n_i,
   input logic [31:0]                         csr_tinfo_q_i,
   input logic                                csr_tinfo_we_i,
   input                                      Dcsr_t csr_dcsr_n_i,
   input                                      Dcsr_t csr_dcsr_q_i,
   input logic                                csr_dcsr_we_i,
   input logic                                csr_debug_csr_save_i,
   input logic [31:0]                         csr_dpc_n_i,
   input logic [31:0]                         csr_dpc_q_i,
   input logic                                csr_dpc_we_i,
   input logic [31:0]                         csr_dscratch0_n_i,
   input logic [31:0]                         csr_dscratch0_q_i,
   input logic                                csr_dscratch0_we_i,
   input logic [31:0]                         csr_dscratch1_n_i,
   input logic [31:0]                         csr_dscratch1_q_i,
   input logic                                csr_dscratch1_we_i,

   // performance counters
   //  cycle,  instret,  hpcounter,  cycleh,  instreth,  hpcounterh
   // mcycle, minstret, mhpcounter, mcycleh, minstreth, mhpcounterh
   input logic [31:0] [MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_n_i,
   input logic [31:0] [MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_q_i,
   input logic [31:0] [MHPMCOUNTER_WORDS-1:0] csr_mhpmcounter_we_i,

   input logic [31:0]                         csr_mvendorid_i,
   input logic [31:0]                         csr_marchid_i,
   input logic [31:0]                         csr_mhartid_i,


  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follow,
  // the convention of RISC-V Formal Interface Specification.
   output logic [ 0:0]                        rvfi_valid,
   output logic [63:0]                        rvfi_order,
   output logic [31:0]                        rvfi_insn,
   output logic [ 0:0]                        rvfi_trap,
   output logic [ 0:0]                        rvfi_halt,
   output logic [ 0:0]                        rvfi_intr,
   output logic [ 1:0]                        rvfi_mode,
   output logic [ 1:0]                        rvfi_ixl,
   output logic [ 0:0]                        rvfi_dbg, // TODO: Rename to rvfi_debug

   output logic [ 4:0]                        rvfi_rs1_addr,
   output logic [ 4:0]                        rvfi_rs2_addr,
   output logic [31:0]                        rvfi_rs1_rdata,
   output logic [31:0]                        rvfi_rs2_rdata,
   output logic [ 4:0]                        rvfi_rd_addr,
   output logic [31:0]                        rvfi_rd_wdata,
   output logic [31:0]                        rvfi_pc_rdata,
   output logic [31:0]                        rvfi_pc_wdata,
   output logic [31:0]                        rvfi_mem_addr,
   output logic [ 3:0]                        rvfi_mem_rmask,
   output logic [ 3:0]                        rvfi_mem_wmask,
   output logic [31:0]                        rvfi_mem_rdata,
   output logic [31:0]                        rvfi_mem_wdata,

   // CSRs
   output logic [31:0]                        rvfi_csr_mstatus_rmask,
   output logic [31:0]                        rvfi_csr_mstatus_wmask,
   output logic [31:0]                        rvfi_csr_mstatus_rdata,
   output logic [31:0]                        rvfi_csr_mstatus_wdata,
   output logic [31:0]                        rvfi_csr_misa_rmask,
   output logic [31:0]                        rvfi_csr_misa_wmask,
   output logic [31:0]                        rvfi_csr_misa_rdata,
   output logic [31:0]                        rvfi_csr_misa_wdata,
   output logic [31:0]                        rvfi_csr_mie_rmask,
   output logic [31:0]                        rvfi_csr_mie_wmask,
   output logic [31:0]                        rvfi_csr_mie_rdata,
   output logic [31:0]                        rvfi_csr_mie_wdata,
   output logic [31:0]                        rvfi_csr_mtvec_rmask,
   output logic [31:0]                        rvfi_csr_mtvec_wmask,
   output logic [31:0]                        rvfi_csr_mtvec_rdata,
   output logic [31:0]                        rvfi_csr_mtvec_wdata,
   output logic [31:0]                        rvfi_csr_mcountinhibit_rmask,
   output logic [31:0]                        rvfi_csr_mcountinhibit_wmask,
   output logic [31:0]                        rvfi_csr_mcountinhibit_rdata,
   output logic [31:0]                        rvfi_csr_mcountinhibit_wdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmevent_rmask, // 3-31 implemented
   output logic [31:0] [31:0]                 rvfi_csr_mhpmevent_wmask,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmevent_rdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmevent_wdata,
   output logic [31:0]                        rvfi_csr_mscratch_rmask,
   output logic [31:0]                        rvfi_csr_mscratch_wmask,
   output logic [31:0]                        rvfi_csr_mscratch_rdata,
   output logic [31:0]                        rvfi_csr_mscratch_wdata,
   output logic [31:0]                        rvfi_csr_mepc_rmask,
   output logic [31:0]                        rvfi_csr_mepc_wmask,
   output logic [31:0]                        rvfi_csr_mepc_rdata,
   output logic [31:0]                        rvfi_csr_mepc_wdata,
   output logic [31:0]                        rvfi_csr_mcause_rmask,
   output logic [31:0]                        rvfi_csr_mcause_wmask,
   output logic [31:0]                        rvfi_csr_mcause_rdata,
   output logic [31:0]                        rvfi_csr_mcause_wdata,
   output logic [31:0]                        rvfi_csr_mtval_rmask,
   output logic [31:0]                        rvfi_csr_mtval_wmask,
   output logic [31:0]                        rvfi_csr_mtval_rdata,
   output logic [31:0]                        rvfi_csr_mtval_wdata,
   output logic [31:0]                        rvfi_csr_mip_rmask,
   output logic [31:0]                        rvfi_csr_mip_wmask,
   output logic [31:0]                        rvfi_csr_mip_rdata,
   output logic [31:0]                        rvfi_csr_mip_wdata,
   output logic [31:0]                        rvfi_csr_tselect_rmask,
   output logic [31:0]                        rvfi_csr_tselect_wmask,
   output logic [31:0]                        rvfi_csr_tselect_rdata,
   output logic [31:0]                        rvfi_csr_tselect_wdata,
   output logic [ 3:0] [31:0]                 rvfi_csr_tdata_rmask, // 1-3 implemented
   output logic [ 3:0] [31:0]                 rvfi_csr_tdata_wmask,
   output logic [ 3:0] [31:0]                 rvfi_csr_tdata_rdata,
   output logic [ 3:0] [31:0]                 rvfi_csr_tdata_wdata,
   output logic [31:0]                        rvfi_csr_tinfo_rmask,
   output logic [31:0]                        rvfi_csr_tinfo_wmask,
   output logic [31:0]                        rvfi_csr_tinfo_rdata,
   output logic [31:0]                        rvfi_csr_tinfo_wdata,
   output logic [31:0]                        rvfi_csr_mcontext_rmask,
   output logic [31:0]                        rvfi_csr_mcontext_wmask,
   output logic [31:0]                        rvfi_csr_mcontext_rdata,
   output logic [31:0]                        rvfi_csr_mcontext_wdata,
   output logic [31:0]                        rvfi_csr_scontext_rmask,
   output logic [31:0]                        rvfi_csr_scontext_wmask,
   output logic [31:0]                        rvfi_csr_scontext_rdata,
   output logic [31:0]                        rvfi_csr_scontext_wdata,
   output logic [31:0]                        rvfi_csr_dcsr_rmask,
   output logic [31:0]                        rvfi_csr_dcsr_wmask,
   output logic [31:0]                        rvfi_csr_dcsr_rdata,
   output logic [31:0]                        rvfi_csr_dcsr_wdata,
   output logic [31:0]                        rvfi_csr_dpc_rmask,
   output logic [31:0]                        rvfi_csr_dpc_wmask,
   output logic [31:0]                        rvfi_csr_dpc_rdata,
   output logic [31:0]                        rvfi_csr_dpc_wdata,
   output logic [ 1:0] [31:0]                 rvfi_csr_dscratch_rmask, // 0-1 implemented
   output logic [ 1:0] [31:0]                 rvfi_csr_dscratch_wmask,
   output logic [ 1:0] [31:0]                 rvfi_csr_dscratch_rdata,
   output logic [ 1:0] [31:0]                 rvfi_csr_dscratch_wdata,
   output logic [31:0]                        rvfi_csr_mcycle_rmask,
   output logic [31:0]                        rvfi_csr_mcycle_wmask,
   output logic [31:0]                        rvfi_csr_mcycle_rdata,
   output logic [31:0]                        rvfi_csr_mcycle_wdata,
   output logic [31:0]                        rvfi_csr_minstret_rmask,
   output logic [31:0]                        rvfi_csr_minstret_wmask,
   output logic [31:0]                        rvfi_csr_minstret_rdata,
   output logic [31:0]                        rvfi_csr_minstret_wdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounter_rmask, // 3-31 implemented
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounter_wmask,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounter_rdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounter_wdata,
   output logic [31:0]                        rvfi_csr_mcycleh_rmask,
   output logic [31:0]                        rvfi_csr_mcycleh_wmask,
   output logic [31:0]                        rvfi_csr_mcycleh_rdata,
   output logic [31:0]                        rvfi_csr_mcycleh_wdata,
   output logic [31:0]                        rvfi_csr_minstreth_rmask,
   output logic [31:0]                        rvfi_csr_minstreth_wmask,
   output logic [31:0]                        rvfi_csr_minstreth_rdata,
   output logic [31:0]                        rvfi_csr_minstreth_wdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounterh_rmask, // 3-31 implemented
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounterh_wmask,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounterh_rdata,
   output logic [31:0] [31:0]                 rvfi_csr_mhpmcounterh_wdata,
   output logic [31:0]                        rvfi_csr_cycle_rmask,
   output logic [31:0]                        rvfi_csr_cycle_wmask,
   output logic [31:0]                        rvfi_csr_cycle_rdata,
   output logic [31:0]                        rvfi_csr_cycle_wdata,
   output logic [31:0]                        rvfi_csr_instret_rmask,
   output logic [31:0]                        rvfi_csr_instret_wmask,
   output logic [31:0]                        rvfi_csr_instret_rdata,
   output logic [31:0]                        rvfi_csr_instret_wdata,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounter_rmask, // 3-31 implemented
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounter_wmask,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounter_rdata,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounter_wdata,
   output logic [31:0]                        rvfi_csr_cycleh_rmask,
   output logic [31:0]                        rvfi_csr_cycleh_wmask,
   output logic [31:0]                        rvfi_csr_cycleh_rdata,
   output logic [31:0]                        rvfi_csr_cycleh_wdata,
   output logic [31:0]                        rvfi_csr_instreth_rmask,
   output logic [31:0]                        rvfi_csr_instreth_wmask,
   output logic [31:0]                        rvfi_csr_instreth_rdata,
   output logic [31:0]                        rvfi_csr_instreth_wdata,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounterh_rmask, // 3-31 implemented
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounterh_wmask,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounterh_rdata,
   output logic [31:0] [31:0]                 rvfi_csr_hpmcounterh_wdata,
   output logic [31:0]                        rvfi_csr_mvendorid_rmask,
   output logic [31:0]                        rvfi_csr_mvendorid_wmask,
   output logic [31:0]                        rvfi_csr_mvendorid_rdata,
   output logic [31:0]                        rvfi_csr_mvendorid_wdata,
   output logic [31:0]                        rvfi_csr_marchid_rmask,
   output logic [31:0]                        rvfi_csr_marchid_wmask,
   output logic [31:0]                        rvfi_csr_marchid_rdata,
   output logic [31:0]                        rvfi_csr_marchid_wdata,
   output logic [31:0]                        rvfi_csr_mimpid_rmask,
   output logic [31:0]                        rvfi_csr_mimpid_wmask,
   output logic [31:0]                        rvfi_csr_mimpid_rdata,
   output logic [31:0]                        rvfi_csr_mimpid_wdata,
   output logic [31:0]                        rvfi_csr_mhartid_rmask,
   output logic [31:0]                        rvfi_csr_mhartid_wmask,
   output logic [31:0]                        rvfi_csr_mhartid_rdata,
   output logic [31:0]                        rvfi_csr_mhartid_wdata
);

  // Propagating from ID stage
  logic [1:0] [31:0] pc_wdata;
  logic [1:0]        debug;
  logic [1:0] [ 4:0] rs1_addr;
  logic [1:0] [ 4:0] rs2_addr;
  logic [1:0] [31:0] rs1_rdata;
  logic [1:0] [31:0] rs2_rdata;
  logic [1:0] [31:0] mem_rmask;
  logic [1:0] [31:0] mem_wmask;

  //Propagating from EX stage
  logic [31:0]       ex_mem_addr;
  logic [31:0]       ex_mem_wdata;

  logic [ 3:0] rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_addr_d;


  logic [31:0] rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_d;

  // CSR inputs in struct format
  rvfi_csr_map_t rvfi_csr_rdata_d;
  rvfi_csr_map_t rvfi_csr_wdata_d;
  rvfi_csr_map_t rvfi_csr_wmask_d;

  rvfi_csr_map_t rvfi_csr_rdata;
  rvfi_csr_map_t rvfi_csr_wdata;
  rvfi_csr_map_t rvfi_csr_wmask;

  // Reads from autonomous registers propagate from EX stage
  rvfi_auto_csr_map_t ex_csr_rdata;
  rvfi_auto_csr_map_t ex_csr_rdata_d;

  logic [31:0][31:0] csr_mhpmcounter_n_l;
  logic [31:0][31:0] csr_mhpmcounter_n_h;
  logic [31:0][31:0] csr_mhpmcounter_q_l;
  logic [31:0][31:0] csr_mhpmcounter_q_h;
  logic [31:0][31:0] csr_mhpmcounter_we_l;
  logic [31:0][31:0] csr_mhpmcounter_we_h;

  logic [63:0] lsu_wdata_ror; // Intermediate rotate signal, as direct part-select not supported in all tools

  logic         intr_d;

  logic         is_debug_entry_if;
  logic         is_debug_entry_id;
  logic         is_jump_id;
  logic         is_branch_ex;
  logic         is_exception_wb;
  logic         is_exception_wb_q;
  logic         is_exception_wb_qq;
  logic         is_dret_wb;
  logic         branch_taken_ex;

  logic [6:0]   insn_opcode;
  logic [4:0]   insn_rd;
  logic [2:0]   insn_funct3;
  logic [4:0]   insn_rs1;
  logic [4:0]   insn_rs2;
  logic [6:0]   insn_funct7;
  logic [11:0]  insn_csr;

  assign insn_opcode = rvfi_insn[6:0];
  assign insn_rd     = rvfi_insn[11:7];
  assign insn_funct3 = rvfi_insn[14:12];
  assign insn_rs1    = rvfi_insn[19:15];
  assign insn_rs2    = rvfi_insn[24:20];
  assign insn_funct7 = rvfi_insn[31:25];
  assign insn_csr    = rvfi_insn[31:20];

`ifdef CV32E40X_TRACE_EXECUTION
  `include "cv32e40x_rvfi_trace.svh"
`endif

  localparam STAGE_ID = 0;
  localparam STAGE_EX = 1;

  rvfi_intr_t  instr_q;

  assign is_debug_entry_if = (pc_mux_i == PC_EXCEPTION) && (exc_pc_mux_i == EXC_PC_DBD);
  assign is_jump_id        = (pc_mux_i == PC_JUMP);
  assign is_branch_ex      = (pc_mux_i == PC_BRANCH);
  assign is_exception_wb   = (pc_mux_i == PC_EXCEPTION);
  assign is_dret_wb        = (pc_mux_i == PC_DRET);

  assign branch_taken_ex   = !lsu_en_ex_i &&
                             (pc_set_i && is_branch_ex) &&
                             !(illegal_insn_ex_i || insn_mret_ex_i || insn_ebrk_ex_i || insn_ecall_ex_i || insn_fencei_ex_i);

    // Assign rvfi channels
  assign rvfi_halt              = 1'b0; // No intruction causing halt in cv32e40x
  assign rvfi_intr              = intr_d;
  assign rvfi_mode              = 2'b11; // Privilege level: Machine-mode (3)
  assign rvfi_ixl               = 2'b01; // XLEN for current privilege level, must be 1(32) for RV32 systems

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_q           <= '0;
    end else begin
      // Store last valid instructions
      if(rvfi_valid) begin
        instr_q.valid    <= rvfi_valid && !is_dret_wb;
        instr_q.order    <= rvfi_order;
        instr_q.pc_wdata <= rvfi_pc_wdata;
      end else begin
        instr_q          <= instr_q;
      end
    end
  end // always_ff @

  // Check if instruction is the first instruction in trap handler
  assign intr_d = rvfi_valid                          && // Current instruction valid
                  instr_q.valid                       && // Previous instruction valid
                  ((rvfi_order - instr_q.order) == 1) && // Is latest instruction
                  (rvfi_pc_rdata != instr_q.pc_wdata);   // Is first part of trap handler


  // Pipeline stage model //

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      is_debug_entry_id  <= 1'b0;
      pc_wdata           <= '0;
      debug              <= 1'b0;
      rs1_addr           <= '0;
      rs2_addr           <= '0;
      rs1_rdata          <= '0;
      rs2_rdata          <= '0;
      mem_rmask          <= '0;
      mem_wmask          <= '0;
      ex_mem_addr        <= '0;
      ex_mem_wdata       <= '0;
      ex_csr_rdata  <= '0;

      is_exception_wb_q  <= 1'b0;
      is_exception_wb_qq <= 1'b0;

      rvfi_dbg           <= '0;
      rvfi_valid         <= 1'b0;
      rvfi_order         <= '0;
      rvfi_insn          <= '0;
      rvfi_pc_rdata      <= '0;
      rvfi_pc_wdata      <= '0;
      rvfi_trap          <= 1'b0;
      rvfi_rd_addr       <= '0;
      rvfi_rd_wdata      <= '0;
      rvfi_csr_rdata     <= '0;
      rvfi_csr_wdata     <= '0;
      rvfi_csr_wmask     <= '0;
      rvfi_rs1_addr      <= '0;
      rvfi_rs2_addr      <= '0;
      rvfi_rs1_rdata     <= '0;
      rvfi_rs2_rdata     <= '0;
      rvfi_mem_addr      <= '0;
      rvfi_mem_rmask     <= '0;
      rvfi_mem_rdata     <= '0;
      rvfi_mem_wmask     <= '0;
      rvfi_mem_wdata     <= '0;

    end else begin

      //// ID Stage ////
      if(instr_id_valid_i && instr_ex_ready_i) begin
        is_debug_entry_id   <= is_debug_entry_if;
        debug    [STAGE_ID] <= is_debug_entry_id;
        pc_wdata [STAGE_ID] <= (pc_set_i && is_jump_id) ? jump_target_id_i : pc_if_i;
        rs1_addr [STAGE_ID] <= rs1_addr_id_i;
        rs2_addr [STAGE_ID] <= rs2_addr_id_i;
        rs1_rdata[STAGE_ID] <= (rs1_addr_id_i != '0)         ? rs1_rdata_id_i    : '0;
        rs2_rdata[STAGE_ID] <= (rs2_addr_id_i != '0)         ? rs2_rdata_id_i    : '0;
        mem_rmask[STAGE_ID] <= (lsu_en_id_i && !lsu_we_id_i) ? rvfi_mem_mask_int : '0;
        mem_wmask[STAGE_ID] <= (lsu_en_id_i &&  lsu_we_id_i) ? rvfi_mem_mask_int : '0;
      end else begin
        is_debug_entry_id   <= is_debug_entry_if || is_debug_entry_id;
      end


      //// EX Stage ////
      if (instr_ex_valid_i && wb_ready_i) begin
        pc_wdata [STAGE_EX] <= branch_taken_ex ? branch_target_ex_i : pc_wdata[STAGE_ID];
        debug    [STAGE_EX] <= debug    [STAGE_ID];
        rs1_addr [STAGE_EX] <= rs1_addr [STAGE_ID];
        rs2_addr [STAGE_EX] <= rs2_addr [STAGE_ID];
        rs1_rdata[STAGE_EX] <= rs1_rdata[STAGE_ID];
        rs2_rdata[STAGE_EX] <= rs2_rdata[STAGE_ID];
        mem_rmask[STAGE_EX] <= mem_rmask[STAGE_ID];
        mem_wmask[STAGE_EX] <= mem_wmask[STAGE_ID];

        // Keep values when misaligned
        ex_mem_addr         <= (lsu_misaligned_ex_i) ? ex_mem_addr  : rvfi_mem_addr_d;
        ex_mem_wdata        <= (lsu_misaligned_ex_i) ? ex_mem_wdata : rvfi_mem_wdata_d;

        // Read autonomuos CSRs from EX perspective
        ex_csr_rdata        <= ex_csr_rdata_d;

      end


      //// WB Stage ////
      rvfi_valid      <= wb_valid_i;
      if (wb_valid_i) begin
        rvfi_order      <= rvfi_order + 64'b1;
        rvfi_dbg        <= debug[STAGE_EX];
        rvfi_pc_rdata   <= pc_wb_i;
        rvfi_insn       <= instr_rdata_wb_i;
        rvfi_trap       <= illegal_insn_wb_i; // todo: factor in other trap conditions

        rvfi_mem_rdata  <= lsu_rdata_wb_i;

        rvfi_rd_addr    <= rvfi_rd_addr_d;
        rvfi_rd_wdata   <= rvfi_rd_wdata_d;

        // Read/Write CSRs
        rvfi_csr_rdata  <= rvfi_csr_rdata_d;
        rvfi_csr_wdata  <= rvfi_csr_wdata_d;
        rvfi_csr_wmask  <= rvfi_csr_wmask_d;

        rvfi_rs1_addr  <= rs1_addr [STAGE_EX];
        rvfi_rs2_addr  <= rs2_addr [STAGE_EX];
        rvfi_rs1_rdata <= rs1_rdata[STAGE_EX];
        rvfi_rs2_rdata <= rs2_rdata[STAGE_EX];
        rvfi_mem_rmask <= mem_rmask[STAGE_EX];
        rvfi_mem_wmask <= mem_wmask[STAGE_EX];
        rvfi_mem_addr  <= ex_mem_addr;
        rvfi_mem_wdata <= ex_mem_wdata;
      end

      if (csr_mstatus_we_i) begin
        rvfi_csr_wdata.mstatus <= rvfi_csr_wdata_d.mstatus;
        rvfi_csr_wmask.mstatus <= rvfi_csr_wmask_d.mstatus;
      end

      // Set expected next PC, half-word aligned
      if (insn_ebrk_wb_i || insn_ecall_wb_i) begin //ebreaks, ecall
        rvfi_pc_wdata <= exception_target_wb_i & ~32'b1;
      end else if (insn_mret_wb_i) begin // mret
        rvfi_pc_wdata <= mepc_target_wb_i & ~32'b1;
      end else begin
        rvfi_pc_wdata <= pc_wdata[STAGE_EX] & ~32'b1;
      end

      // CSR special cases // todo: Explain this circuit; why is there a need for is_exception_wb_q and is_exception_wb_qq?
      if (is_exception_wb || is_exception_wb_q) begin // todo: align wit Oystein on naming
        is_exception_wb_q  <= is_exception_wb;
        is_exception_wb_qq <= is_exception_wb_q;
        rvfi_csr_wmask.mstatus <= '0;
      end else if (is_exception_wb_qq) begin
        if (wb_valid_i || insn_mret_wb_i || (lsu_rvalid_wb_i && lsu_en_wb_i)) begin
          is_exception_wb_qq <= 1'b0;
          rvfi_csr_wdata.mstatus <= csr_mstatus_q_i; // Take value already stored in mstatus
          rvfi_csr_wmask.mstatus <= '1;
        end else begin
          is_exception_wb_qq <= 1'b1;
          rvfi_csr_wmask.mstatus <= '0;
        end
      end

      if (csr_debug_csr_save_i && rvfi_valid) begin
        rvfi_csr_wmask.dcsr <= csr_dcsr_we_i ? '1 : '0;
        rvfi_csr_wdata.dcsr <= csr_dcsr_n_i;
        rvfi_csr_rdata.dcsr <= csr_dcsr_n_i;
      end

    end
  end

  //////////////////


  // Byte enable based on data type
  always_comb begin
    unique case (lsu_type_id_i)
      2'b00:   rvfi_mem_mask_int = 4'b0001;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b1111;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  // Memory adddress
  assign rvfi_mem_addr_d = lsu_addr_ex_i;

  // Align Memory write data
  assign rvfi_mem_wdata_d  = lsu_wdata_ror[31:0];
  assign lsu_wdata_ror     = {lsu_wdata_ex_i, lsu_wdata_ex_i} >> (8*rvfi_mem_addr_d[1:0]); // Rotate right

  // Destination Register
  assign rvfi_rd_addr_d  = (rd_we_wb_i)           ? rd_addr_wb_i  : '0;
  assign rvfi_rd_wdata_d = (rvfi_rd_addr_d != '0) ? rd_wdata_wb_i : '0;

  ////////////////////////////////
  //  CSRs                      //
  ////////////////////////////////

  // Machine trap setup
  assign rvfi_csr_rdata_d.mstatus            = csr_mstatus_q_i;
  assign rvfi_csr_wdata_d.mstatus            = csr_mstatus_n_i;
  assign rvfi_csr_wmask_d.mstatus            = csr_mstatus_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.misa               = csr_misa_n_i;
  assign rvfi_csr_wdata_d.misa               = csr_misa_q_i;
  assign rvfi_csr_wmask_d.misa               = csr_misa_we_i    ? '1 : '0;

  assign rvfi_csr_rdata_d.mie                = csr_mie_q_i;
  assign rvfi_csr_wdata_d.mie                = csr_mie_n_i;
  assign rvfi_csr_wmask_d.mie                = csr_mie_we_i     ? '1 : '0;

  assign rvfi_csr_rdata_d.mtvec              = csr_mtvec_q_i;
  assign rvfi_csr_wdata_d.mtvec              = csr_mtvec_n_i;
  assign rvfi_csr_wmask_d.mtvec              = csr_mtvec_we_i   ? '1 : '0;

  // Performance counters
  assign rvfi_csr_rdata_d.mcountinhibit      = csr_mcountinhibit_q_i;
  assign rvfi_csr_wdata_d.mcountinhibit      = csr_mcountinhibit_n_i;
  assign rvfi_csr_wmask_d.mcountinhibit      = csr_mcountinhibit_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mhpmevent          = csr_mhpmevent_q_i;
  assign rvfi_csr_wdata_d.mhpmevent          = csr_mhpmevent_n_i;
  assign rvfi_csr_mhpmevent_wmask[2:0]       = '0; // No mhpevent0-2 registers
  assign rvfi_csr_mhpmevent_wmask[31:3]      = csr_mhpmevent_we_i ? '1 : '0;

  // Machine trap handling
  assign rvfi_csr_rdata_d.mscratch           = csr_mscratch_q_i;
  assign rvfi_csr_wdata_d.mscratch           = csr_mscratch_n_i;
  assign rvfi_csr_wmask_d.mscratch           = csr_mscratch_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mepc               = csr_mepc_q_i;
  assign rvfi_csr_wdata_d.mepc               = csr_mepc_n_i;
  assign rvfi_csr_wmask_d.mepc               = csr_mepc_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mcause             = csr_mcause_q_i;
  assign rvfi_csr_wdata_d.mcause             = csr_mcause_n_i;
  assign rvfi_csr_wmask_d.mcause             = csr_mcause_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mtval              = '0;
  assign rvfi_csr_wdata_d.mtval              = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mtval              = '0;

  assign ex_csr_rdata_d.mip                  = csr_mip_q_i;
  assign rvfi_csr_rdata_d.mip                = ex_csr_rdata.mip;
  assign rvfi_csr_wdata_d.mip                = csr_mip_n_i;
  assign rvfi_csr_wmask_d.mip                = csr_mip_we_i ? '1 : '0;

  // Trigger
  assign rvfi_csr_rdata_d.tselect            = '0;
  assign rvfi_csr_wdata_d.tselect            = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.tselect            = '0;

  assign rvfi_csr_rdata_d.tdata[0]           = 'Z;
  assign rvfi_csr_wdata_d.tdata[0]           = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.tdata[0]           = '0;

  assign rvfi_csr_rdata_d.tdata[1]           = csr_tdata1_q_i;
  assign rvfi_csr_wdata_d.tdata[1]           = csr_tdata1_n_i;
  assign rvfi_csr_wmask_d.tdata[1]           = csr_tdata1_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.tdata[2]           = csr_tdata2_q_i;
  assign rvfi_csr_wdata_d.tdata[2]           = csr_tdata2_n_i;
  assign rvfi_csr_wmask_d.tdata[2]           = csr_tdata2_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.tdata[3]           = '0;
  assign rvfi_csr_wdata_d.tdata[3]           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.tdata[3]           = '0;

  assign rvfi_csr_rdata_d.tinfo              = csr_tinfo_n_i;
  assign rvfi_csr_wdata_d.tinfo              = csr_tinfo_q_i;
  assign rvfi_csr_wmask_d.tinfo              = csr_tinfo_we_i;

  assign rvfi_csr_rdata_d.mcontext           = '0;
  assign rvfi_csr_wdata_d.mcontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mcontext           = '0;

  assign rvfi_csr_rdata_d.scontext           = '0;
  assign rvfi_csr_wdata_d.scontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.scontext           = '0;

  // Debug / Trace
  assign rvfi_csr_rdata_d.dcsr               = csr_dcsr_q_i;
  assign rvfi_csr_wdata_d.dcsr               = csr_dcsr_n_i;
  assign rvfi_csr_wmask_d.dcsr               = csr_dcsr_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.dpc                = csr_dpc_q_i;
  assign rvfi_csr_wdata_d.dpc                = csr_dpc_n_i;
  assign rvfi_csr_wmask_d.dpc                = csr_dpc_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.dscratch[0]        = csr_dscratch0_q_i;
  assign rvfi_csr_wdata_d.dscratch[0]        = csr_dscratch0_n_i;
  assign rvfi_csr_wmask_d.dscratch[0]        = csr_dscratch0_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.dscratch[1]        = csr_dscratch1_q_i;
  assign rvfi_csr_wdata_d.dscratch[1]        = csr_dscratch1_n_i;
  assign rvfi_csr_wmask_d.dscratch[1]        = csr_dscratch1_we_i ? '1 : '0;

  // Performance Monitors
  generate
    for (genvar i = 0; i < 32; i++) begin
      assign csr_mhpmcounter_n_l[i]  = csr_mhpmcounter_n_i[i][31: 0];
      assign csr_mhpmcounter_n_h[i]  = csr_mhpmcounter_n_i[i][63:32];
      assign csr_mhpmcounter_q_l[i]  = csr_mhpmcounter_q_i[i][31: 0];
      assign csr_mhpmcounter_q_h[i]  = csr_mhpmcounter_q_i[i][63:32];
      assign csr_mhpmcounter_we_l[i] = csr_mhpmcounter_we_i[i][0] ? '1 : '0;
      assign csr_mhpmcounter_we_h[i] = csr_mhpmcounter_we_i[i][1] ? '1 : '0;
    end
  endgenerate

  assign ex_csr_rdata_d.mcycle               = csr_mhpmcounter_q_l [CSR_MCYCLE & 'hF];
  assign rvfi_csr_rdata_d.mcycle             = ex_csr_rdata.mcycle;
  assign rvfi_csr_wdata_d.mcycle             = csr_mhpmcounter_n_l [CSR_MCYCLE & 'hF];
  assign rvfi_csr_wmask_d.mcycle             = csr_mhpmcounter_we_l[CSR_MCYCLE & 'hF];

  assign rvfi_csr_rdata_d.minstret           = csr_mhpmcounter_q_l [CSR_MINSTRET & 'hF];
  assign rvfi_csr_wdata_d.minstret           = csr_mhpmcounter_q_l [CSR_MINSTRET & 'hF];
  assign rvfi_csr_wmask_d.minstret           = csr_mhpmcounter_we_l[CSR_MINSTRET & 'hF];

  assign rvfi_csr_rdata_d.mhpmcounter[ 2:0]  = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounter[ 2:0]  = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounter[ 2:0]  = '0;
  assign rvfi_csr_rdata_d.mhpmcounter[31:3]  = csr_mhpmcounter_q_l [31:3];
  assign rvfi_csr_wdata_d.mhpmcounter[31:3]  = csr_mhpmcounter_q_l [31:3];
  assign rvfi_csr_wmask_d.mhpmcounter[31:3]  = csr_mhpmcounter_we_l[31:3];

  assign ex_csr_rdata_d.mcycleh              = csr_mhpmcounter_q_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_rdata_d.mcycleh            = ex_csr_rdata.mcycleh;
  assign rvfi_csr_wdata_d.mcycleh            = csr_mhpmcounter_n_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_wmask_d.mcycleh            = csr_mhpmcounter_we_h[CSR_MCYCLEH & 'hF];

  assign rvfi_csr_rdata_d.minstreth          = csr_mhpmcounter_q_h [CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wdata_d.minstreth          = csr_mhpmcounter_n_h [CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wmask_d.minstreth          = csr_mhpmcounter_we_h[CSR_MINSTRETH & 'hF];

  assign rvfi_csr_rdata_d.mhpmcounterh[ 2:0] = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounterh[ 2:0] = 'Z;  // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounterh[ 2:0] = '0;
  assign rvfi_csr_rdata_d.mhpmcounterh[31:3] = csr_mhpmcounter_q_h [31:3];
  assign rvfi_csr_wdata_d.mhpmcounterh[31:3] = csr_mhpmcounter_n_h [31:3];
  assign rvfi_csr_wmask_d.mhpmcounterh[31:3] = csr_mhpmcounter_we_h[31:3];

  assign ex_csr_rdata_d.cycle                = csr_mhpmcounter_q_l [CSR_CYCLE & 'hF];
  assign rvfi_csr_rdata_d.cycle              = ex_csr_rdata.cycle;
  assign rvfi_csr_wdata_d.cycle              = csr_mhpmcounter_n_l [CSR_CYCLE & 'hF];
  assign rvfi_csr_wmask_d.cycle              = csr_mhpmcounter_we_l[CSR_CYCLE & 'hF];

  assign rvfi_csr_rdata_d.instret            = csr_mhpmcounter_q_l [CSR_INSTRET & 'hF];
  assign rvfi_csr_wdata_d.instret            = csr_mhpmcounter_n_l [CSR_INSTRET & 'hF];
  assign rvfi_csr_wmask_d.instret            = csr_mhpmcounter_we_l[CSR_INSTRET & 'hF];

  assign rvfi_csr_rdata_d.hpmcounter[ 2:0]   = 'Z;
  assign rvfi_csr_wdata_d.hpmcounter[ 2:0]   = 'Z;  // Does not exist
  assign rvfi_csr_wmask_d.hpmcounter[ 2:0]   = '0;
  assign rvfi_csr_rdata_d.hpmcounter[31:3]   = csr_mhpmcounter_q_l [31:3];
  assign rvfi_csr_wdata_d.hpmcounter[31:3]   = csr_mhpmcounter_n_l [31:3];
  assign rvfi_csr_wmask_d.hpmcounter[31:3]   = csr_mhpmcounter_we_l[31:3];

  assign ex_csr_rdata_d.cycleh               = csr_mhpmcounter_q_h [CSR_CYCLEH & 'hF];
  assign rvfi_csr_rdata_d.cycleh             = ex_csr_rdata.cycleh;
  assign rvfi_csr_wdata_d.cycleh             = csr_mhpmcounter_n_h [CSR_CYCLEH & 'hF];
  assign rvfi_csr_wmask_d.cycleh             = csr_mhpmcounter_we_h[CSR_CYCLEH & 'hF];

  assign rvfi_csr_rdata_d.instreth           = csr_mhpmcounter_q_h [CSR_INSTRETH & 'hF];
  assign rvfi_csr_wdata_d.instreth           = csr_mhpmcounter_n_h [CSR_INSTRETH & 'hF];
  assign rvfi_csr_wmask_d.instreth           = csr_mhpmcounter_we_h[CSR_INSTRETH & 'hF];

  assign rvfi_csr_rdata_d.hpmcounterh[ 2:0]  = 'Z;
  assign rvfi_csr_wdata_d.hpmcounterh[ 2:0]  = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.hpmcounterh[ 2:0]  = '0;
  assign rvfi_csr_rdata_d.hpmcounterh[31:3]  = csr_mhpmcounter_q_h [31:3];
  assign rvfi_csr_wdata_d.hpmcounterh[31:3]  = csr_mhpmcounter_n_h [31:3];
  assign rvfi_csr_wmask_d.hpmcounterh[31:3]  = csr_mhpmcounter_we_h[31:3];

  // Machine info
  assign rvfi_csr_rdata_d.mvendorid          = csr_mvendorid_i;
  assign rvfi_csr_wdata_d.mvendorid          = '0; // Read Only
  assign rvfi_csr_wmask_d.mvendorid          = '0;

  assign rvfi_csr_wdata_d.marchid            = '0; // Read Only
  assign rvfi_csr_wmask_d.marchid            = '0;
  assign rvfi_csr_rdata_d.marchid            = csr_marchid_i;

  assign rvfi_csr_wdata_d.mimpid             = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mimpid             = '0;
  assign rvfi_csr_rdata_d.mimpid             = '0;

  assign rvfi_csr_wdata_d.mhartid            = '0; // Read Only
  assign rvfi_csr_wmask_d.mhartid            = '0;
  assign rvfi_csr_rdata_d.mhartid            = csr_mhartid_i;


  // CSR outputs //
  assign rvfi_csr_mstatus_rdata           = rvfi_csr_rdata.mstatus;
  assign rvfi_csr_mstatus_rmask           = '1;
  assign rvfi_csr_mstatus_wdata           = rvfi_csr_wdata.mstatus;
  assign rvfi_csr_mstatus_wmask           = rvfi_csr_wmask.mstatus;
  assign rvfi_csr_misa_rdata              = rvfi_csr_rdata.misa;
  assign rvfi_csr_misa_rmask              = '1;
  assign rvfi_csr_misa_wdata              = rvfi_csr_wdata.misa;
  assign rvfi_csr_misa_wmask              = rvfi_csr_wmask.misa;
  assign rvfi_csr_mie_rdata               = rvfi_csr_rdata.mie;
  assign rvfi_csr_mie_rmask               = '1;
  assign rvfi_csr_mie_wdata               = rvfi_csr_wdata.mie;
  assign rvfi_csr_mie_wmask               = rvfi_csr_wmask.mie;
  assign rvfi_csr_mtvec_rdata             = rvfi_csr_rdata.mtvec;
  assign rvfi_csr_mtvec_rmask             = '1;
  assign rvfi_csr_mtvec_wdata             = rvfi_csr_wdata.mtvec;
  assign rvfi_csr_mtvec_wmask             = rvfi_csr_wmask.mtvec;
  assign rvfi_csr_mcountinhibit_rdata     = rvfi_csr_rdata.mcountinhibit;
  assign rvfi_csr_mcountinhibit_rmask     = '1;
  assign rvfi_csr_mcountinhibit_wdata     = rvfi_csr_wdata.mcountinhibit;
  assign rvfi_csr_mcountinhibit_wmask     = rvfi_csr_wmask.mcountinhibit;
  assign rvfi_csr_mhpmevent_rdata         = rvfi_csr_rdata.mhpmevent;
  assign rvfi_csr_mhpmevent_rmask[ 2:0]   = '1;
  assign rvfi_csr_mhpmevent_rmask[31:3]   = '1;
  assign rvfi_csr_mhpmevent_wdata         = rvfi_csr_wdata.mhpmevent;
  assign rvfi_csr_mhpmevent_wmask         = rvfi_csr_wmask.mhpmevent;
  assign rvfi_csr_mscratch_rdata          = rvfi_csr_rdata.mscratch;
  assign rvfi_csr_mscratch_rmask          = '1;
  assign rvfi_csr_mscratch_wdata          = rvfi_csr_wdata.mscratch;
  assign rvfi_csr_mscratch_wmask          = rvfi_csr_wmask.mscratch;
  assign rvfi_csr_mepc_rdata              = rvfi_csr_rdata.mepc;
  assign rvfi_csr_mepc_rmask              = '1;
  assign rvfi_csr_mepc_wdata              = rvfi_csr_wdata.mepc;
  assign rvfi_csr_mepc_wmask              = rvfi_csr_wmask.mepc;
  assign rvfi_csr_mcause_rdata            = rvfi_csr_rdata.mcause;
  assign rvfi_csr_mcause_rmask            = '1;
  assign rvfi_csr_mcause_wdata            = rvfi_csr_wdata.mcause;
  assign rvfi_csr_mcause_wmask            = rvfi_csr_wmask.mcause;
  assign rvfi_csr_mtval_rdata             = rvfi_csr_rdata.mtval;
  assign rvfi_csr_mtval_rmask             = '1;
  assign rvfi_csr_mtval_wdata             = rvfi_csr_wdata.mtval;
  assign rvfi_csr_mtval_wmask             = rvfi_csr_wmask.mtval;
  assign rvfi_csr_mip_rdata               = rvfi_csr_rdata.mip;
  assign rvfi_csr_mip_rmask               = '1;
  assign rvfi_csr_mip_wdata               = rvfi_csr_wdata.mip;
  assign rvfi_csr_mip_wmask               = rvfi_csr_wmask.mip;
  assign rvfi_csr_tselect_rdata           = rvfi_csr_rdata.tselect;
  assign rvfi_csr_tselect_rmask           = '1;
  assign rvfi_csr_tselect_wdata           = rvfi_csr_wdata.tselect;
  assign rvfi_csr_tselect_wmask           = rvfi_csr_wmask.tselect;
  assign rvfi_csr_tdata_rdata             = rvfi_csr_rdata.tdata;
  assign rvfi_csr_tdata_rmask[0]          = '0; // Does not exist
  assign rvfi_csr_tdata_rmask[3:1]        = '1;
  assign rvfi_csr_tdata_wdata             = rvfi_csr_wdata.tdata;
  assign rvfi_csr_tdata_wmask             = rvfi_csr_wmask.tdata;
  assign rvfi_csr_tinfo_rdata             = rvfi_csr_rdata.tinfo;
  assign rvfi_csr_tinfo_rmask             = '1;
  assign rvfi_csr_tinfo_wdata             = rvfi_csr_wdata.tinfo;
  assign rvfi_csr_tinfo_wmask             = rvfi_csr_wmask.tinfo;
  assign rvfi_csr_mcontext_rdata          = rvfi_csr_rdata.mcontext;
  assign rvfi_csr_mcontext_rmask          = '1;
  assign rvfi_csr_mcontext_wdata          = rvfi_csr_wdata.mcontext;
  assign rvfi_csr_mcontext_wmask          = rvfi_csr_wmask.mcontext;
  assign rvfi_csr_scontext_rdata          = rvfi_csr_rdata.scontext;
  assign rvfi_csr_scontext_rmask          = '1;
  assign rvfi_csr_scontext_wdata          = rvfi_csr_wdata.scontext;
  assign rvfi_csr_scontext_wmask          = rvfi_csr_wmask.scontext;
  assign rvfi_csr_dcsr_rdata              = rvfi_csr_rdata.dcsr;
  assign rvfi_csr_dcsr_rmask              = '1;
  assign rvfi_csr_dcsr_wdata              = rvfi_csr_wdata.dcsr;
  assign rvfi_csr_dcsr_wmask              = rvfi_csr_wmask.dcsr;
  assign rvfi_csr_dpc_rdata               = rvfi_csr_rdata.dpc;
  assign rvfi_csr_dpc_rmask               = '1;
  assign rvfi_csr_dpc_wdata               = rvfi_csr_wdata.dpc;
  assign rvfi_csr_dpc_wmask               = rvfi_csr_wmask.dpc;
  assign rvfi_csr_dscratch_rdata          = rvfi_csr_rdata.dscratch;
  assign rvfi_csr_dscratch_rmask          = '1;
  assign rvfi_csr_dscratch_wdata          = rvfi_csr_wdata.dscratch;
  assign rvfi_csr_dscratch_wmask          = rvfi_csr_wmask.dscratch;
  assign rvfi_csr_mcycle_rdata            = rvfi_csr_rdata.mcycle;
  assign rvfi_csr_mcycle_rmask            = '1;
  assign rvfi_csr_mcycle_wdata            = rvfi_csr_wdata.mcycle;
  assign rvfi_csr_mcycle_wmask            = rvfi_csr_wmask.mcycle;
  assign rvfi_csr_minstret_rdata          = rvfi_csr_rdata.minstret;
  assign rvfi_csr_minstret_rmask          = '1;
  assign rvfi_csr_minstret_wdata          = rvfi_csr_wdata.minstret;
  assign rvfi_csr_minstret_wmask          = rvfi_csr_wmask.minstret;
  assign rvfi_csr_mhpmcounter_rdata       = rvfi_csr_rdata.mhpmcounter;
  assign rvfi_csr_mhpmcounter_rmask[ 2:0] = '0;
  assign rvfi_csr_mhpmcounter_rmask[31:3] = '1;
  assign rvfi_csr_mhpmcounter_wdata       = rvfi_csr_wdata.mhpmcounter;
  assign rvfi_csr_mhpmcounter_wmask       = rvfi_csr_wmask.mhpmcounter;
  assign rvfi_csr_mcycleh_rdata           = rvfi_csr_rdata.mcycleh;
  assign rvfi_csr_mcycleh_rmask           = '1;
  assign rvfi_csr_mcycleh_wdata           = rvfi_csr_wdata.mcycleh;
  assign rvfi_csr_mcycleh_wmask           = rvfi_csr_wmask.mcycleh;
  assign rvfi_csr_minstreth_rdata         = rvfi_csr_rdata.minstreth;
  assign rvfi_csr_minstreth_rmask         = '1;
  assign rvfi_csr_minstreth_wdata         = rvfi_csr_wdata.minstreth;
  assign rvfi_csr_minstreth_wmask         = rvfi_csr_wmask.minstreth;
  assign rvfi_csr_mhpmcounterh_rdata      = rvfi_csr_rdata.mhpmcounterh;
  assign rvfi_csr_mhpmcounterh_rmask[ 2:0] = '0;
  assign rvfi_csr_mhpmcounterh_rmask[31:3] = '1;
  assign rvfi_csr_mhpmcounterh_wdata      = rvfi_csr_wdata.mhpmcounterh;
  assign rvfi_csr_mhpmcounterh_wmask      = rvfi_csr_wmask.mhpmcounterh;
  assign rvfi_csr_mvendorid_rdata         = rvfi_csr_rdata.mvendorid;
  assign rvfi_csr_mvendorid_rmask         = '1;
  assign rvfi_csr_mvendorid_wdata         = rvfi_csr_wdata.mvendorid;
  assign rvfi_csr_mvendorid_wmask         = rvfi_csr_wmask.mvendorid;
  assign rvfi_csr_marchid_rdata           = rvfi_csr_rdata.marchid;
  assign rvfi_csr_marchid_rmask           = '1;
  assign rvfi_csr_marchid_wdata           = rvfi_csr_wdata.marchid;
  assign rvfi_csr_marchid_wmask           = rvfi_csr_wmask.marchid;
  assign rvfi_csr_mimpid_rdata            = rvfi_csr_rdata.mimpid;
  assign rvfi_csr_mimpid_rmask            = '1;
  assign rvfi_csr_mimpid_wdata            = rvfi_csr_wdata.mimpid;
  assign rvfi_csr_mimpid_wmask            = rvfi_csr_wmask.mimpid;
  assign rvfi_csr_mhartid_rdata           = rvfi_csr_rdata.mhartid;
  assign rvfi_csr_mhartid_rmask           = '1;
  assign rvfi_csr_mhartid_wdata           = rvfi_csr_wdata.mhartid;
  assign rvfi_csr_mhartid_wmask           = rvfi_csr_wmask.mhartid;
  assign rvfi_csr_cycle_rdata             = rvfi_csr_rdata.cycle;
  assign rvfi_csr_cycle_rmask             = '1;
  assign rvfi_csr_cycle_wdata             = rvfi_csr_wdata.cycle;
  assign rvfi_csr_cycle_wmask             = rvfi_csr_wmask.cycle;
  assign rvfi_csr_instret_rdata           = rvfi_csr_rdata.instret;
  assign rvfi_csr_instret_rmask           = '1;
  assign rvfi_csr_instret_wdata           = rvfi_csr_wdata.instret;
  assign rvfi_csr_instret_wmask           = rvfi_csr_wmask.instret;
  assign rvfi_csr_hpmcounter_rdata        = rvfi_csr_rdata.hpmcounter;
  assign rvfi_csr_hpmcounter_rmask[ 2:0]  = '0;
  assign rvfi_csr_hpmcounter_rmask[31:3]  = '1;
  assign rvfi_csr_hpmcounter_wdata        = rvfi_csr_wdata.hpmcounter;
  assign rvfi_csr_hpmcounter_wmask        = rvfi_csr_wmask.hpmcounter;
  assign rvfi_csr_cycleh_rdata            = rvfi_csr_rdata.cycleh;
  assign rvfi_csr_cycleh_rmask            = '1;
  assign rvfi_csr_cycleh_wdata            = rvfi_csr_wdata.cycleh;
  assign rvfi_csr_cycleh_wmask            = rvfi_csr_wmask.cycleh;
  assign rvfi_csr_instreth_rdata          = rvfi_csr_rdata.instreth;
  assign rvfi_csr_instreth_rmask          = '1;
  assign rvfi_csr_instreth_wdata          = rvfi_csr_wdata.instreth;
  assign rvfi_csr_instreth_wmask          = rvfi_csr_wmask.instreth;
  assign rvfi_csr_hpmcounterh_rdata       = rvfi_csr_rdata.hpmcounterh;
  assign rvfi_csr_hpmcounterh_rmask[ 2:0] = '0;
  assign rvfi_csr_hpmcounterh_rmask[31:3] = '1;
  assign rvfi_csr_hpmcounterh_wdata       = rvfi_csr_wdata.hpmcounterh;
  assign rvfi_csr_hpmcounterh_wmask       = rvfi_csr_wmask.hpmcounterh;

endmodule // cv32e40x_rvfi

