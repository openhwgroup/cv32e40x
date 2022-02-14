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
   input logic                                if_valid_i,
   input logic [31:0]                         pc_if_i,
   input logic                                instr_pmp_err_if_i,

   //// ID probes ////
   input logic [31:0]                         pc_id_i,
   input logic                                id_valid_i,
   input logic                                id_ready_i,
   input logic [ 1:0]                         rf_re_id_i,
   input logic                                sys_en_id_i,
   input logic                                sys_mret_insn_id_i,
   input logic                                jump_in_id_i,
   input logic [31:0]                         jump_target_id_i,
   input logic                                is_compressed_id_i,
   // LSU
   input logic                                lsu_en_id_i,
   input logic                                lsu_we_id_i,
   input logic [1:0]                          lsu_size_id_i,
   // Register reads
   input logic [4:0]                          rs1_addr_id_i,
   input logic [4:0]                          rs2_addr_id_i,
   input logic [31:0]                         operand_a_fw_id_i,
   input logic [31:0]                         operand_b_fw_id_i,

   //// EX probes ////
   input logic                                branch_in_ex_i,
   // LSU
   input logic                                lsu_en_ex_i,
   input logic                                lsu_pmp_err_ex_i,
   input logic                                lsu_pma_err_atomic_ex_i,

   input logic                                ex_ready_i,
   input logic                                ex_valid_i,

   input logic [31:0]                         branch_target_ex_i,

   input logic [31:0]                         data_addr_ex_i,
   input logic [31:0]                         data_wdata_ex_i,
   input logic                                lsu_split_q_ex_i,

   //// WB probes ////
   input logic [31:0]                         pc_wb_i,
   input logic                                wb_ready_i,
   input logic                                wb_valid_i,
   input logic                                ebreak_in_wb_i,
   input logic [31:0]                         instr_rdata_wb_i,
   // Register writes
   input logic                                rf_we_wb_i,
   input logic [4:0]                          rf_addr_wb_i,
   input logic [31:0]                         rf_wdata_wb_i,
   // LSU
   input logic [31:0]                         lsu_rdata_wb_i,
   // PC //
   input logic [31:0]                         branch_addr_n_i,

   input                                      privlvl_t priv_lvl_i,

   // Controller FSM probe
   input ctrl_fsm_t                           ctrl_fsm_i,
   input logic                                pending_single_step_i,
   input logic                                single_step_allowed_i,
   input logic                                nmi_pending_i,
   input logic                                nmi_is_store_i,

   //// CSR Probes ////
   input                                      jvt_t csr_jvt_n_i,
   input                                      jvt_t csr_jvt_q_i,
   input logic                                csr_jvt_we_i,
   input                                      mstatus_t csr_mstatus_n_i,
   input                                      mstatus_t csr_mstatus_q_i,
   input logic                                csr_mstatus_we_i,
   input                                      mstatush_t csr_mstatush_n_i,
   input                                      mstatush_t csr_mstatush_q_i,
   input logic                                csr_mstatush_we_i,
   input logic [31:0]                         csr_misa_n_i,
   input logic [31:0]                         csr_misa_q_i,
   input logic                                csr_misa_we_i,
   input logic [31:0]                         csr_mie_n_i,
   input logic [31:0]                         csr_mie_q_i,
   input logic                                csr_mie_we_i,
   input                                      mtvec_t csr_mtvec_n_i,
   input                                      mtvec_t csr_mtvec_q_i,
   input logic                                csr_mtvec_we_i,
   input                                      mtvt_t csr_mtvt_n_i,
   input                                      mtvt_t csr_mtvt_q_i,
   input logic                                csr_mtvt_we_i,
   input logic [31:0]                         csr_mcountinhibit_n_i,
   input logic [31:0]                         csr_mcountinhibit_q_i,
   input logic                                csr_mcountinhibit_we_i,
   input logic [31:0] [31:0]                  csr_mhpmevent_n_i,
   input logic [31:0] [31:0]                  csr_mhpmevent_q_i,
   input logic [31:0]                         csr_mhpmevent_we_i,
   input logic [31:0]                         csr_mscratch_n_i,
   input logic [31:0]                         csr_mscratch_q_i,
   input logic                                csr_mscratch_we_i,
   input logic [31:0]                         csr_mepc_n_i,
   input logic [31:0]                         csr_mepc_q_i,
   input logic                                csr_mepc_we_i,
   input                                      mcause_t csr_mcause_n_i,
   input                                      mcause_t csr_mcause_q_i,
   input logic                                csr_mcause_we_i,
   input logic [31:0]                         csr_mip_n_i,
   input logic [31:0]                         csr_mip_q_i,
   input logic                                csr_mip_we_i,
   input logic [31:0]                         csr_mnxti_n_i,
   input logic [31:0]                         csr_mnxti_q_i,
   input logic                                csr_mnxti_we_i,
   input                                      mintstatus_t csr_mintstatus_n_i,
   input                                      mintstatus_t csr_mintstatus_q_i,
   input logic                                csr_mintstatus_we_i,
   input logic [31:0]                         csr_mintthresh_n_i,
   input logic [31:0]                         csr_mintthresh_q_i,
   input logic                                csr_mintthresh_we_i,
   input logic [31:0]                         csr_mscratchcsw_n_i,
   input logic [31:0]                         csr_mscratchcsw_q_i,
   input logic                                csr_mscratchcsw_we_i,
   input logic [31:0]                         csr_mscratchcswl_n_i,
   input logic [31:0]                         csr_mscratchcswl_q_i,
   input logic                                csr_mscratchcswl_we_i,
   input logic [31:0]                         csr_mclicbase_n_i,
   input logic [31:0]                         csr_mclicbase_q_i,
   input logic                                csr_mclicbase_we_i,
   input logic [31:0]                         csr_tdata1_n_i,
   input logic [31:0]                         csr_tdata1_q_i,
   input logic                                csr_tdata1_we_i,
   input logic [31:0]                         csr_tdata2_n_i,
   input logic [31:0]                         csr_tdata2_q_i,
   input logic                                csr_tdata2_we_i,
   input logic [31:0]                         csr_tinfo_n_i,
   input logic [31:0]                         csr_tinfo_q_i,
   input logic                                csr_tinfo_we_i,
   input logic [31:0]                         csr_tcontrol_n_i,
   input logic [31:0]                         csr_tcontrol_q_i,
   input logic                                csr_tcontrol_we_i,
   input                                      dcsr_t csr_dcsr_n_i,
   input                                      dcsr_t csr_dcsr_q_i,
   input logic                                csr_dcsr_we_i,
   input logic [31:0]                         csr_dpc_n_i,
   input logic [31:0]                         csr_dpc_q_i,
   input logic                                csr_dpc_we_i,
   input logic [31:0]                         csr_dscratch0_n_i,
   input logic [31:0]                         csr_dscratch0_q_i,
   input logic                                csr_dscratch0_we_i,
   input logic [31:0]                         csr_dscratch1_n_i,
   input logic [31:0]                         csr_dscratch1_q_i,
   input logic                                csr_dscratch1_we_i,
   input logic [31:0]                         csr_mconfigptr_n_i,
   input logic [31:0]                         csr_mconfigptr_q_i,
   input logic                                csr_mconfigptr_we_i,

   // performance counters
   //  cycle,  instret,  hpcounter,  cycleh,  instreth,  hpcounterh
   // mcycle, minstret, mhpcounter, mcycleh, minstreth, mhpcounterh
   input logic [31:0] [MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_n_i,
   input logic [31:0] [MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_q_i,
   input logic [31:0] [MHPMCOUNTER_WORDS-1:0] csr_mhpmcounter_we_i,

   input logic [31:0]                         csr_mvendorid_i,
   input logic [31:0]                         csr_marchid_i,
   input logic [31:0]                         csr_mhartid_i,
   input logic [31:0]                         csr_mimpid_i,

   input logic [31:0]                         csr_mcounteren_n_i,
   input logic [31:0]                         csr_mcounteren_q_i,
   input logic                                csr_mcounteren_we_i,

   input logic [ 7:0]                         csr_pmpcfg_n_i[16],
   input logic [ 7:0]                         csr_pmpcfg_q_i[16],
   input logic [15:0]                         csr_pmpcfg_we_i,
   input logic [31:0]                         csr_pmpaddr_n_i, // PMP address input shared for all pmpaddr registers
   input logic [31:0]                         csr_pmpaddr_q_i[16],
   input logic [15:0]                         csr_pmpaddr_we_i,
   input logic [31:0]                         csr_mseccfg_n_i,
   input logic [31:0]                         csr_mseccfg_q_i,
   input logic                                csr_mseccfg_we_i,
   input logic [31:0]                         csr_mseccfgh_n_i,
   input logic [31:0]                         csr_mseccfgh_q_i,
   input logic                                csr_mseccfgh_we_i,

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follow,
  // the convention of RISC-V Formal Interface Specification.
   output logic [ 0:0]                        rvfi_valid,
   output logic [63:0]                        rvfi_order,
   output logic [31:0]                        rvfi_insn,
   output logic [13:0]                        rvfi_trap,
   output logic [ 0:0]                        rvfi_halt,
   output logic [ 0:0]                        rvfi_intr,
   output logic [ 1:0]                        rvfi_mode,
   output logic [ 1:0]                        rvfi_ixl,
   output logic [ 1:0]                        rvfi_nmip,

   output logic [ 2:0]                        rvfi_dbg,
   output logic [ 0:0]                        rvfi_dbg_mode,

   output logic [ 4:0]                        rvfi_rd_addr,
   output logic [31:0]                        rvfi_rd_wdata,
   output logic [ 4:0]                        rvfi_rs1_addr,
   output logic [ 4:0]                        rvfi_rs2_addr,
   output logic [31:0]                        rvfi_rs1_rdata,
   output logic [31:0]                        rvfi_rs2_rdata,

   output logic [31:0]                        rvfi_pc_rdata,
   output logic [31:0]                        rvfi_pc_wdata,

   output logic [31:0]                        rvfi_mem_addr,
   output logic [ 3:0]                        rvfi_mem_rmask,
   output logic [ 3:0]                        rvfi_mem_wmask,
   output logic [31:0]                        rvfi_mem_rdata,
   output logic [31:0]                        rvfi_mem_wdata,

   // CSRs
   output logic [31:0]                        rvfi_csr_jvt_rmask,
   output logic [31:0]                        rvfi_csr_jvt_wmask,
   output logic [31:0]                        rvfi_csr_jvt_rdata,
   output logic [31:0]                        rvfi_csr_jvt_wdata,
   output logic [31:0]                        rvfi_csr_mstatus_rmask,
   output logic [31:0]                        rvfi_csr_mstatus_wmask,
   output logic [31:0]                        rvfi_csr_mstatus_rdata,
   output logic [31:0]                        rvfi_csr_mstatus_wdata,
   output logic [31:0]                        rvfi_csr_mstatush_rmask,
   output logic [31:0]                        rvfi_csr_mstatush_wmask,
   output logic [31:0]                        rvfi_csr_mstatush_rdata,
   output logic [31:0]                        rvfi_csr_mstatush_wdata,
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
   output logic [31:0]                        rvfi_csr_mtvt_rmask,
   output logic [31:0]                        rvfi_csr_mtvt_wmask,
   output logic [31:0]                        rvfi_csr_mtvt_rdata,
   output logic [31:0]                        rvfi_csr_mtvt_wdata,
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
   output logic [31:0]                        rvfi_csr_mnxti_rmask,
   output logic [31:0]                        rvfi_csr_mnxti_wmask,
   output logic [31:0]                        rvfi_csr_mnxti_rdata,
   output logic [31:0]                        rvfi_csr_mnxti_wdata,
   output logic [31:0]                        rvfi_csr_mintstatus_rmask,
   output logic [31:0]                        rvfi_csr_mintstatus_wmask,
   output logic [31:0]                        rvfi_csr_mintstatus_rdata,
   output logic [31:0]                        rvfi_csr_mintstatus_wdata,
   output logic [31:0]                        rvfi_csr_mintthresh_rmask,
   output logic [31:0]                        rvfi_csr_mintthresh_wmask,
   output logic [31:0]                        rvfi_csr_mintthresh_rdata,
   output logic [31:0]                        rvfi_csr_mintthresh_wdata,
   output logic [31:0]                        rvfi_csr_mscratchcsw_rmask,
   output logic [31:0]                        rvfi_csr_mscratchcsw_wmask,
   output logic [31:0]                        rvfi_csr_mscratchcsw_rdata,
   output logic [31:0]                        rvfi_csr_mscratchcsw_wdata,
   output logic [31:0]                        rvfi_csr_mscratchcswl_rmask,
   output logic [31:0]                        rvfi_csr_mscratchcswl_wmask,
   output logic [31:0]                        rvfi_csr_mscratchcswl_rdata,
   output logic [31:0]                        rvfi_csr_mscratchcswl_wdata,
   output logic [31:0]                        rvfi_csr_mclicbase_rmask,
   output logic [31:0]                        rvfi_csr_mclicbase_wmask,
   output logic [31:0]                        rvfi_csr_mclicbase_rdata,
   output logic [31:0]                        rvfi_csr_mclicbase_wdata,
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
   output logic [31:0]                        rvfi_csr_tcontrol_rmask,
   output logic [31:0]                        rvfi_csr_tcontrol_wmask,
   output logic [31:0]                        rvfi_csr_tcontrol_rdata,
   output logic [31:0]                        rvfi_csr_tcontrol_wdata,
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
   output logic [31:0]                        rvfi_csr_mhartid_wdata,

   output logic [31:0]                        rvfi_csr_mcounteren_rmask,
   output logic [31:0]                        rvfi_csr_mcounteren_wmask,
   output logic [31:0]                        rvfi_csr_mcounteren_rdata,
   output logic [31:0]                        rvfi_csr_mcounteren_wdata,

   output logic [ 3:0] [31:0]                 rvfi_csr_pmpcfg_rmask,
   output logic [ 3:0] [31:0]                 rvfi_csr_pmpcfg_wmask,
   output logic [ 3:0] [31:0]                 rvfi_csr_pmpcfg_rdata,
   output logic [ 3:0] [31:0]                 rvfi_csr_pmpcfg_wdata,
   output logic [15:0] [31:0]                 rvfi_csr_pmpaddr_rmask,
   output logic [15:0] [31:0]                 rvfi_csr_pmpaddr_wmask,
   output logic [15:0] [31:0]                 rvfi_csr_pmpaddr_rdata,
   output logic [15:0] [31:0]                 rvfi_csr_pmpaddr_wdata,
   output logic        [31:0]                 rvfi_csr_mseccfg_rmask,
   output logic        [31:0]                 rvfi_csr_mseccfg_wmask,
   output logic        [31:0]                 rvfi_csr_mseccfg_rdata,
   output logic        [31:0]                 rvfi_csr_mseccfg_wdata,
   output logic        [31:0]                 rvfi_csr_mseccfgh_rmask,
   output logic        [31:0]                 rvfi_csr_mseccfgh_wmask,
   output logic        [31:0]                 rvfi_csr_mseccfgh_rdata,
   output logic        [31:0]                 rvfi_csr_mseccfgh_wdata,

   output logic [31:0]                        rvfi_csr_mconfigptr_rmask,
   output logic [31:0]                        rvfi_csr_mconfigptr_wmask,
   output logic [31:0]                        rvfi_csr_mconfigptr_rdata,
   output logic [31:0]                        rvfi_csr_mconfigptr_wdata
);

  // Propagating from ID stage
  logic [3:0] [31:0] pc_wdata;
  logic [3:0]        debug_mode;
  logic [3:0] [ 2:0] debug_cause;
  logic [3:0]        instr_pmp_err;
  logic [3:0]        in_trap;
  logic [3:0] [ 4:0] rs1_addr;
  logic [3:0] [ 4:0] rs2_addr;
  logic [3:0] [31:0] rs1_rdata;
  logic [3:0] [31:0] rs2_rdata;
  logic [3:0] [ 3:0] mem_rmask;
  logic [3:0] [ 3:0] mem_wmask;

  //Propagating from EX stage
  logic [31:0]       ex_mem_addr;
  logic [31:0]       ex_mem_wdata;
  mem_err_t [3:0]    mem_err;

  logic [ 3:0] rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_addr_d;


  logic [ 4:0] rd_addr_wb;
  logic [31:0] rd_wdata_wb;

  logic [ 4:0] rs1_addr_id;
  logic [ 4:0] rs2_addr_id;
  logic [31:0] rs1_rdata_id;
  logic [31:0] rs2_rdata_id;

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

  // Signals for special handling of performance counters
  logic [31:0][31:0] mhpmcounter_l_rdata_q;
  logic [31:0][31:0] mhpmcounter_l_wdata_q;
  logic [31:0][31:0] mhpmcounter_h_rdata_q;
  logic [31:0][31:0] mhpmcounter_h_wdata_q;

  // Counter was written during WB and possibly before wb_valid
  logic [31:0]       mhpmcounter_l_during_wb;
  logic [31:0]       mhpmcounter_h_during_wb;




  logic [63:0] data_wdata_ror; // Intermediate rotate signal, as direct part-select not supported in all tools

  logic         pc_mux_debug;
  logic         pc_mux_dret;
  logic         pc_mux_exception;
  logic         pc_mux_interrupt;
  logic         pc_mux_nmi;

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

  // The pc_mux signals probe the MUX in the IF stage to extract information about events in the WB stage.
  // These signals are therefore used both in the WB stage to see effects of the executed instruction (e.g. rvfi_trap), and
  // in the IF stage to see the reason for executing the instruction (e.g. rvfi_intr).
  assign pc_mux_interrupt = (ctrl_fsm_i.pc_mux == PC_TRAP_IRQ);
  assign pc_mux_nmi       = (ctrl_fsm_i.pc_mux == PC_TRAP_NMI);
  assign pc_mux_debug     = (ctrl_fsm_i.pc_mux == PC_TRAP_DBD);
  assign pc_mux_exception = (ctrl_fsm_i.pc_mux == PC_TRAP_EXC) || (ctrl_fsm_i.pc_mux == PC_TRAP_DBE);
  assign pc_mux_dret      = (ctrl_fsm_i.pc_mux == PC_DRET);

  // Assign rvfi channels
  assign rvfi_halt = 1'b0; // No intruction causing halt in cv32e40x
  assign rvfi_ixl = 2'b01; // XLEN for current privilege level, must be 1(32) for RV32 systems

  logic         in_trap_clr;
  // Clear in trap pipeline when it reaches rvfi_intr
  // This is done to avoid reporting already signaled triggers as supressed during by debug
  assign in_trap_clr = wb_valid_i && in_trap[STAGE_WB];


  // Set rvfi_trap for instructions causing exception or debug entry.
  logic [13:0]  rvfi_trap_next;

  always_comb begin
    rvfi_trap_next = '0;

    if (pc_mux_debug) begin
      // All debug entries will set pc_mux_debug but only synchronous debug entries will set wb_valid (and in turn rvfi_valid)
      // as asynchronous entries will kill the WB stage whereas synchronous entries will not.
      // Indicate that the trap is a synchronous trap into debug mode
      rvfi_trap_next[2:0]  = 3'b101;
      // Special case for debug entry from debug mode caused by EBREAK as it is not captured by ctrl_fsm_i.debug_cause
      rvfi_trap_next[11:9] = ebreak_in_wb_i ? DBG_CAUSE_EBREAK : ctrl_fsm_i.debug_cause;
    end

    if (pc_mux_exception) begin
      // Indicate synchronous (non-debug entry) trap
      rvfi_trap_next[2:0] = 3'b011;
      rvfi_trap_next[8:3] = ctrl_fsm_i.csr_cause.exception_code;

      // Separate exception causes with the same ecseption cause code
      case (ctrl_fsm_i.csr_cause.exception_code)
        EXC_CAUSE_INSTR_FAULT : begin
          rvfi_trap_next[13:12] = instr_pmp_err[STAGE_WB] ? 2'h1 : 2'h0;
        end
        EXC_CAUSE_BREAKPOINT : begin
          // Todo: Add support for trigger match exceptions when implemented in rtl
        end
        EXC_CAUSE_LOAD_FAULT : begin
          rvfi_trap_next[13:12] = mem_err[STAGE_WB];
        end
        EXC_CAUSE_STORE_FAULT : begin
          rvfi_trap_next[13:12] = mem_err[STAGE_WB];
        end
        default : begin
          // rvfi_trap_next[13:12] are only set for exception codes that can have multiple causes
        end
      endcase // case (ctrl_fsm_i.csr_cause.exception_code)

    end

    if(pending_single_step_i && single_step_allowed_i) begin
      // The timing of the single step debug entry does not allow using pc_mux for detection
      rvfi_trap_next[2:0]  = 3'b101;
      rvfi_trap_next[11:9] = DBG_CAUSE_STEP;
      if (pc_mux_exception) begin
        // Special case, exception in WB and pending single step.
        // Indicate both non-debug trap and trap into debug mode
        rvfi_trap_next[2:0]  = 3'b111;
      end
    end
  end

  // Pipeline stage model //

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_wdata           <= '0;
      in_trap            <= '0;
      debug_mode         <= '0;
      debug_cause        <= '0;
      instr_pmp_err      <= '0;
      rs1_addr           <= '0;
      rs2_addr           <= '0;
      rs1_rdata          <= '0;
      rs2_rdata          <= '0;
      mem_rmask          <= '0;
      mem_wmask          <= '0;
      ex_mem_addr        <= '0;
      ex_mem_wdata       <= '0;
      mem_err            <= '0;
      ex_csr_rdata       <= '0;
      rvfi_dbg           <= '0;
      rvfi_dbg_mode      <= '0;
      rvfi_valid         <= 1'b0;
      rvfi_order         <= '0;
      rvfi_insn          <= '0;
      rvfi_pc_rdata      <= '0;
      rvfi_pc_wdata      <= '0;
      rvfi_trap          <= '0;
      rvfi_intr          <= 1'b0;
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

      //// IF Stage ////
      if (if_valid_i && id_ready_i) begin
        debug_mode [STAGE_ID] <= ctrl_fsm_i.debug_mode; // Probing in IF to ensure LSU instructions that are not killed can complete
        instr_pmp_err[STAGE_ID] <= instr_pmp_err_if_i;    // Instruction fetch pmp error probed to separate pmp- from pma-errors

        // Capturing events that happen when the IF stage is not valid and
        // propagating them through the pipeline with the next valid instruction

        // Capture events
        in_trap    [STAGE_ID] <= in_trap    [STAGE_IF];
        debug_cause[STAGE_ID] <= debug_cause[STAGE_IF];

        // Clear captured events
        in_trap    [STAGE_IF] <= 1'b0;
        debug_cause[STAGE_IF] <= '0;

      end else begin
        if (in_trap_clr) begin
          // Clear interrupt pipeline when it reaches rvfi_intr
          in_trap    [STAGE_ID] <= '0;
        end

        // IF stage is killed and not valid during debug entry. If debug is taken,
        // debug cause is saved to propagate through rvfi pipeline together with next valid instruction
        if (pc_mux_debug) begin
          // Debug cause input only valid during debug taken
          // Special case for debug entry from debug mode caused by EBREAK as it is not captured by ctrl_fsm_i.debug_cause
          // A higher priority debug request (e.g. trigger match) will pull ebreak_in_wb_i low and allow the debug cause to propagate
          debug_cause[STAGE_IF] <=  ebreak_in_wb_i ? 3'h1 : ctrl_fsm_i.debug_cause;

          // If there is a trap in the pipeline when debug is taken, the trap will be supressed but the side-effects will not.
          // The succeeding instruction therefore needs to re-trigger the intr bit if it it did not reach the rvfi output.
          if (|in_trap) begin
            in_trap[STAGE_IF] <= 1'b1;
          end
        end

        // Picking up trap entry when IF is not valid to propagate for next valid instruction
        // The in trap signal is set for the first instruction of interrupt- and exception handlers (not debug handler)
        if (pc_mux_interrupt || pc_mux_nmi || pc_mux_exception) begin
          in_trap[STAGE_IF] <= 1'b1;
        end
      end

      //// ID Stage ////
      if(id_valid_i && ex_ready_i) begin

        if (jump_in_id_i) begin
          // Predicting mret/jump explicitly instead of using branch_addr_n to
          // avoid including asynchronous traps and debug reqs in prediction
          pc_wdata [STAGE_EX] <= (sys_en_id_i && sys_mret_insn_id_i) ? csr_mepc_q_i : jump_target_id_i;
        end else begin
          pc_wdata [STAGE_EX] <= is_compressed_id_i ?  pc_id_i + 2 : pc_id_i + 4;
        end

        in_trap    [STAGE_EX] <= in_trap    [STAGE_ID];
        debug_mode [STAGE_EX] <= debug_mode [STAGE_ID];
        debug_cause[STAGE_EX] <= debug_cause[STAGE_ID];
        instr_pmp_err[STAGE_EX] <= instr_pmp_err[STAGE_ID];
        rs1_addr   [STAGE_EX] <= rs1_addr_id;
        rs2_addr   [STAGE_EX] <= rs2_addr_id;
        rs1_rdata  [STAGE_EX] <= rs1_rdata_id;
        rs2_rdata  [STAGE_EX] <= rs2_rdata_id;
        mem_rmask  [STAGE_EX] <= (lsu_en_id_i && !lsu_we_id_i) ? rvfi_mem_mask_int : '0;
        mem_wmask  [STAGE_EX] <= (lsu_en_id_i &&  lsu_we_id_i) ? rvfi_mem_mask_int : '0;
      end else begin
        if (in_trap_clr) begin
          // Clear interrupt pipeline when it reaches rvfi_intr
          in_trap    [STAGE_EX] <= '0;
        end
      end


      //// EX Stage ////
      if (ex_valid_i && wb_ready_i) begin
        // Predicting branch target explicitly to avoid predicting asynchronous events
        pc_wdata   [STAGE_WB] <= branch_in_ex_i ? branch_target_ex_i : pc_wdata[STAGE_EX];
        debug_mode [STAGE_WB] <= debug_mode         [STAGE_EX];
        debug_cause[STAGE_WB] <= debug_cause        [STAGE_EX];
        instr_pmp_err[STAGE_WB] <= instr_pmp_err    [STAGE_EX];
        rs1_addr   [STAGE_WB] <= rs1_addr           [STAGE_EX];
        rs2_addr   [STAGE_WB] <= rs2_addr           [STAGE_EX];
        rs1_rdata  [STAGE_WB] <= rs1_rdata          [STAGE_EX];
        rs2_rdata  [STAGE_WB] <= rs2_rdata          [STAGE_EX];
        mem_rmask  [STAGE_WB] <= mem_rmask          [STAGE_EX];
        mem_wmask  [STAGE_WB] <= mem_wmask          [STAGE_EX];
        in_trap    [STAGE_WB] <= in_trap            [STAGE_EX];

        if (!lsu_split_q_ex_i) begin
          // The second part of the split misaligned acess is suppressed to keep
          // the start address and data for the whole misaligned transfer
          ex_mem_addr         <= rvfi_mem_addr_d;
          ex_mem_wdata        <= rvfi_mem_wdata_d;
        end

        mem_err   [STAGE_WB]  <= lsu_pmp_err_ex_i        ? MEM_ERR_PMP :
                                 lsu_pma_err_atomic_ex_i ? MEM_ERR_ATOMIC :
                                                           MEM_ERR_IO_ALIGN;

        // Read autonomuos CSRs from EX perspective
        ex_csr_rdata        <= ex_csr_rdata_d;

      end else begin
        if (in_trap_clr) begin
          // Clear interrupt pipeline when it reaches rvfi_intr
          in_trap    [STAGE_WB] <= '0;
        end
      end


      //// WB Stage ////
      rvfi_valid      <= wb_valid_i;
      if (wb_valid_i) begin
        rvfi_order      <= rvfi_order + 64'b1;
        rvfi_pc_rdata   <= pc_wb_i;
        rvfi_insn       <= instr_rdata_wb_i;

        rvfi_trap       <= rvfi_trap_next;

        rvfi_mem_rdata  <= lsu_rdata_wb_i;

        rvfi_rd_addr    <= rd_addr_wb;
        rvfi_rd_wdata   <= rd_wdata_wb;

        // Read/Write CSRs
        rvfi_csr_rdata  <= rvfi_csr_rdata_d;
        rvfi_csr_wdata  <= rvfi_csr_wdata_d;
        rvfi_csr_wmask  <= rvfi_csr_wmask_d;

        rvfi_intr      <= in_trap   [STAGE_WB];
        rvfi_rs1_addr  <= rs1_addr  [STAGE_WB];
        rvfi_rs2_addr  <= rs2_addr  [STAGE_WB];
        rvfi_rs1_rdata <= rs1_rdata [STAGE_WB];
        rvfi_rs2_rdata <= rs2_rdata [STAGE_WB];
        rvfi_mem_rmask <= mem_rmask [STAGE_WB];
        rvfi_mem_wmask <= mem_wmask [STAGE_WB];
        rvfi_mem_addr  <= ex_mem_addr;
        rvfi_mem_wdata <= ex_mem_wdata;

        rvfi_mode      <= priv_lvl_i;

        rvfi_dbg       <= debug_cause[STAGE_WB];
        rvfi_dbg_mode  <= debug_mode [STAGE_WB];

        // Set expected next PC, half-word aligned
        // Predict synchronous exceptions and synchronous debug entry in WB to include all causes
        rvfi_pc_wdata <= (pc_mux_debug || pc_mux_exception) ? branch_addr_n_i & ~32'b1 :
                         (pc_mux_dret) ? csr_dpc_q_i :
                         pc_wdata[STAGE_WB] & ~32'b1;
      end

    end
  end // always_ff @

  assign rvfi_nmip = {nmi_is_store_i, nmi_pending_i};

  // Capture possible performance counter writes during WB, before wb_valid
  // If counter write happens before wb_valid (LSU stalled waiting for rvalid for example),
  // we must keep _n and _q values to correctly set _rdata and _wdata when rvfi_valid is set.
  // If wb_valid occurs in the same cycle as the write, the flags are zero and any
  // stored values will not be used.
  generate for (genvar i = 0; i < 32; i++)
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mhpmcounter_l_rdata_q[i] <= '0;
        mhpmcounter_h_rdata_q[i] <= '0;
        mhpmcounter_l_wdata_q[i] <= '0;
        mhpmcounter_h_wdata_q[i] <= '0;
        mhpmcounter_l_during_wb[i] <= 1'b0;
        mhpmcounter_h_during_wb[i] <= 1'b0;
      end else begin
        // Clear flags on wb_valid
        if (wb_valid_i) begin
          mhpmcounter_l_during_wb[i] <= 1'b0;
          mhpmcounter_h_during_wb[i] <= 1'b0;
        end else begin
          // Capture counter writes.
          if (csr_mhpmcounter_we_l[i]) begin
            mhpmcounter_l_during_wb[i] <= 1'b1;
            mhpmcounter_l_rdata_q[i]   <= csr_mhpmcounter_q_l[i];
            mhpmcounter_l_wdata_q[i]   <= csr_mhpmcounter_n_l[i];
          end

          if (csr_mhpmcounter_we_h[i]) begin
            mhpmcounter_h_during_wb[i] <= 1'b1;
            mhpmcounter_h_rdata_q[i]   <= csr_mhpmcounter_q_h[i];
            mhpmcounter_h_wdata_q[i]   <= csr_mhpmcounter_n_h[i];
          end
        end
      end
    end
  endgenerate
  //////////////////


  // Byte enable based on data size
  always_comb begin
    unique case (lsu_size_id_i)
      2'b00:   rvfi_mem_mask_int = 4'b0001;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b1111;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  // Memory adddress
  assign rvfi_mem_addr_d = data_addr_ex_i;

  // Align Memory write data
  assign rvfi_mem_wdata_d  = data_wdata_ror[31:0];
  assign data_wdata_ror    = {data_wdata_ex_i, data_wdata_ex_i} >> (8*rvfi_mem_addr_d[1:0]); // Rotate right

  // Destination Register
  // The rd_addr signal in rtl can contain contain unused non-zero values when not reading
  assign rd_addr_wb  = (rf_we_wb_i)      ? rf_addr_wb_i  : '0;
  assign rd_wdata_wb = (rd_addr_wb != 0) ? rf_wdata_wb_i : '0; // Gating wdata for x0 as it is assigned to 0
                                                               // in RTL regardless of wdata (which can be non-zero)

  // Source Register Read Data
  // Setting register read data from operands if there was a read and clearing if there was not as operands can contain
  // data that is not read from the register file when not reading (e.g. for immediate instructions).
  // Can't use register file rdata directly as forwarded data is needed for instructions using the same register back-to-back
  assign rs1_rdata_id = (rf_re_id_i[0]) ? operand_a_fw_id_i : '0;
  assign rs2_rdata_id = (rf_re_id_i[1]) ? operand_b_fw_id_i : '0;
  // The rs* address signals can contain unused non-zero values when not reading
  assign rs1_addr_id  = (rf_re_id_i[0]) ? rs1_addr_id_i     : '0;
  assign rs2_addr_id  = (rf_re_id_i[1]) ? rs2_addr_id_i     : '0;

  ////////////////////////////////
  //  CSRs                      //
  ////////////////////////////////

  // Zc* Register (Jump Vector Table)
  assign rvfi_csr_rdata_d.jvt                = csr_jvt_q_i;
  assign rvfi_csr_wdata_d.jvt                = csr_jvt_n_i;
  assign rvfi_csr_wmask_d.jvt                = csr_jvt_we_i ? '1 : '0;

  // Machine trap setup
  assign rvfi_csr_rdata_d.mstatus            = csr_mstatus_q_i;
  assign rvfi_csr_wdata_d.mstatus            = csr_mstatus_n_i;
  assign rvfi_csr_wmask_d.mstatus            = csr_mstatus_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mstatush           = csr_mstatush_q_i;
  assign rvfi_csr_wdata_d.mstatush           = csr_mstatush_n_i;
  assign rvfi_csr_wmask_d.mstatush           = csr_mstatush_we_i ? '1 : '0;
// todo: misa assignments seem swapped
  assign rvfi_csr_rdata_d.misa               = csr_misa_n_i;
  assign rvfi_csr_wdata_d.misa               = csr_misa_q_i;
  assign rvfi_csr_wmask_d.misa               = csr_misa_we_i    ? '1 : '0;

  assign rvfi_csr_rdata_d.mie                = csr_mie_q_i;
  assign rvfi_csr_wdata_d.mie                = csr_mie_n_i;
  assign rvfi_csr_wmask_d.mie                = csr_mie_we_i     ? '1 : '0;

  assign rvfi_csr_rdata_d.mtvec              = csr_mtvec_q_i;
  assign rvfi_csr_wdata_d.mtvec              = csr_mtvec_n_i;
  assign rvfi_csr_wmask_d.mtvec              = csr_mtvec_we_i   ? '1 : '0;

  assign rvfi_csr_rdata_d.mtvt               = csr_mtvt_q_i;
  assign rvfi_csr_wdata_d.mtvt               = csr_mtvt_n_i;
  assign rvfi_csr_wmask_d.mtvt               = csr_mtvt_we_i   ? '1 : '0;

  // Performance counters
  assign rvfi_csr_rdata_d.mcountinhibit      = csr_mcountinhibit_q_i;
  assign rvfi_csr_wdata_d.mcountinhibit      = csr_mcountinhibit_n_i;
  assign rvfi_csr_wmask_d.mcountinhibit      = csr_mcountinhibit_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mhpmevent          = csr_mhpmevent_q_i;
  assign rvfi_csr_wdata_d.mhpmevent          = csr_mhpmevent_n_i;
  assign rvfi_csr_wmask_d.mhpmevent[2:0]     = '0; // No mhpevent0-2 registers
  generate for (genvar i = 3; i < 32; i++)
    assign rvfi_csr_wmask_d.mhpmevent[i]     = csr_mhpmevent_we_i[i] ? '1 : '0;
  endgenerate

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

  assign rvfi_csr_rdata_d.mnxti              = csr_mnxti_q_i;
  assign rvfi_csr_wdata_d.mnxti              = csr_mnxti_n_i;
  assign rvfi_csr_wmask_d.mnxti              = csr_mnxti_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mintstatus         = csr_mintstatus_q_i;
  assign rvfi_csr_wdata_d.mintstatus         = csr_mintstatus_n_i;
  assign rvfi_csr_wmask_d.mintstatus         = csr_mintstatus_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mintthresh         = csr_mintthresh_q_i;
  assign rvfi_csr_wdata_d.mintthresh         = csr_mintthresh_n_i;
  assign rvfi_csr_wmask_d.mintthresh         = csr_mintthresh_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mscratchcsw        = csr_mscratchcsw_q_i;
  assign rvfi_csr_wdata_d.mscratchcsw        = csr_mscratchcsw_n_i;
  assign rvfi_csr_wmask_d.mscratchcsw        = csr_mscratchcsw_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mscratchcswl       = csr_mscratchcswl_q_i;
  assign rvfi_csr_wdata_d.mscratchcswl       = csr_mscratchcswl_n_i;
  assign rvfi_csr_wmask_d.mscratchcswl       = csr_mscratchcswl_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mclicbase          = csr_mclicbase_q_i;
  assign rvfi_csr_wdata_d.mclicbase          = csr_mclicbase_n_i;
  assign rvfi_csr_wmask_d.mclicbase          = csr_mclicbase_we_i ? '1 : '0;

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

  assign rvfi_csr_rdata_d.tinfo              = csr_tinfo_q_i;
  assign rvfi_csr_wdata_d.tinfo              = csr_tinfo_n_i;
  assign rvfi_csr_wmask_d.tinfo              = csr_tinfo_we_i;

  assign rvfi_csr_rdata_d.tcontrol           = csr_tcontrol_q_i;
  assign rvfi_csr_wdata_d.tcontrol           = csr_tcontrol_n_i;
  assign rvfi_csr_wmask_d.tcontrol           = csr_tcontrol_we_i ? '1 : '0;
  // TODO: do not tie off mcontext inside the module
  assign rvfi_csr_rdata_d.mcontext           = '0;
  assign rvfi_csr_wdata_d.mcontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mcontext           = '0;

  assign rvfi_csr_rdata_d.scontext           = '0;
  assign rvfi_csr_wdata_d.scontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.scontext           = '0;

  // Debug / Trace
  assign ex_csr_rdata_d.nmip                 = csr_dcsr_q_i[3]; // dcsr.nmip is autonomous. Propagate read value from EX stage
  assign rvfi_csr_rdata_d.dcsr               = {csr_dcsr_q_i[31:4], ex_csr_rdata.nmip, csr_dcsr_q_i[2:0]};
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

  // Used flopped values in case write happened before wb_valid
  assign rvfi_csr_rdata_d.minstret           = !mhpmcounter_l_during_wb[CSR_MINSTRET & 'hF] ? csr_mhpmcounter_q_l [CSR_MINSTRET & 'hF] : mhpmcounter_l_rdata_q[CSR_MINSTRET & 'hF];
  assign rvfi_csr_wdata_d.minstret           = !mhpmcounter_l_during_wb[CSR_MINSTRET & 'hF] ? csr_mhpmcounter_n_l [CSR_MINSTRET & 'hF] : mhpmcounter_l_wdata_q[CSR_MINSTRET & 'hF];
  assign rvfi_csr_wmask_d.minstret           = !mhpmcounter_l_during_wb[CSR_MINSTRET & 'hF] ? csr_mhpmcounter_we_l[CSR_MINSTRET & 'hF] : '1;

  assign rvfi_csr_rdata_d.mhpmcounter[ 2:0]  = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounter[ 2:0]  = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounter[ 2:0]  = '0;

  // Used flopped values in case write happened before wb_valid
  generate
    for (genvar i = 3; i < 32; i++) begin
      assign rvfi_csr_rdata_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_q_l [i] : mhpmcounter_l_rdata_q[i];
      assign rvfi_csr_wdata_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_n_l [i] : mhpmcounter_l_wdata_q[i];
      assign rvfi_csr_wmask_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_we_l[i] : '1;
    end
  endgenerate

  assign ex_csr_rdata_d.mcycleh              = csr_mhpmcounter_q_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_rdata_d.mcycleh            = ex_csr_rdata.mcycleh;
  assign rvfi_csr_wdata_d.mcycleh            = csr_mhpmcounter_n_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_wmask_d.mcycleh            = csr_mhpmcounter_we_h[CSR_MCYCLEH & 'hF];

  // Used flopped values in case write happened before wb_valid
  assign rvfi_csr_rdata_d.minstreth          = !mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_q_h [CSR_MINSTRETH & 'hF] : mhpmcounter_h_rdata_q[CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wdata_d.minstreth          = !mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_n_h [CSR_MINSTRETH & 'hF] : mhpmcounter_h_wdata_q[CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wmask_d.minstreth          = !mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_we_h[CSR_MINSTRETH & 'hF] : '1;

  assign rvfi_csr_rdata_d.mhpmcounterh[ 2:0] = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounterh[ 2:0] = 'Z;  // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounterh[ 2:0] = '0;

  // Used flopped values in case write happened before wb_valid
  generate
    for (genvar i = 3; i < 32; i++) begin
      assign rvfi_csr_rdata_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_q_h [i] : mhpmcounter_h_rdata_q[i];
      assign rvfi_csr_wdata_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_n_h [i] : mhpmcounter_h_wdata_q[i];
      assign rvfi_csr_wmask_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_we_h[i] : '1;
    end
  endgenerate

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

  assign rvfi_csr_wdata_d.mimpid             = '0; // Read Only
  assign rvfi_csr_wmask_d.mimpid             = '0;
  assign rvfi_csr_rdata_d.mimpid             = csr_mimpid_i;

  assign rvfi_csr_wdata_d.mhartid            = '0; // Read Only
  assign rvfi_csr_wmask_d.mhartid            = '0;
  assign rvfi_csr_rdata_d.mhartid            = csr_mhartid_i;

  // User Mode
  assign rvfi_csr_rdata_d.mcounteren         = csr_mcounteren_q_i;
  assign rvfi_csr_wdata_d.mcounteren         = csr_mcounteren_n_i;
  assign rvfi_csr_wmask_d.mcounteren         = csr_mcounteren_we_i ? '1 : '0;

  // PMP
  // Special case for the PMP cfg registers because they are split by pmp region and not by register
  generate
    for (genvar i = 0; i < 16; i++ ) begin // Max 16 pmp regions
      // 4 regions in each register
      assign rvfi_csr_wdata_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_n_i[i];
      assign rvfi_csr_rdata_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_q_i[i];
      assign rvfi_csr_wmask_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_we_i[i] ? '1 : '0;

      assign rvfi_csr_wdata_d.pmpaddr[i]          = csr_pmpaddr_n_i; // input shared between all registers
      assign rvfi_csr_rdata_d.pmpaddr[i]          = csr_pmpaddr_q_i[i];
    assign rvfi_csr_wmask_d.pmpaddr[i]       = csr_pmpaddr_we_i[i] ? '1 : '0;
    end
  endgenerate

  assign rvfi_csr_wdata_d.mseccfg         = csr_mseccfg_n_i;
  assign rvfi_csr_rdata_d.mseccfg         = csr_mseccfg_q_i;
  assign rvfi_csr_wmask_d.mseccfg         = csr_mseccfg_we_i ? '1 : '0;
  assign rvfi_csr_wdata_d.mseccfgh        = csr_mseccfgh_n_i;
  assign rvfi_csr_rdata_d.mseccfgh        = csr_mseccfgh_q_i;
  assign rvfi_csr_wmask_d.mseccfgh        = csr_mseccfgh_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mconfigptr      = csr_mconfigptr_q_i;
  assign rvfi_csr_wdata_d.mconfigptr      = csr_mconfigptr_n_i;
  assign rvfi_csr_wmask_d.mconfigptr      = csr_mconfigptr_we_i ? '1 : '0;

  // CSR outputs //
  assign rvfi_csr_jvt_rdata               = rvfi_csr_rdata.jvt;
  assign rvfi_csr_jvt_rmask               = '1;
  assign rvfi_csr_jvt_wdata               = rvfi_csr_wdata.jvt;
  assign rvfi_csr_jvt_wmask               = rvfi_csr_wmask.jvt;
  assign rvfi_csr_mstatus_rdata           = rvfi_csr_rdata.mstatus;
  assign rvfi_csr_mstatus_rmask           = '1;
  assign rvfi_csr_mstatus_wdata           = rvfi_csr_wdata.mstatus;
  assign rvfi_csr_mstatus_wmask           = rvfi_csr_wmask.mstatus;
  assign rvfi_csr_mstatush_rdata          = rvfi_csr_rdata.mstatush;
  assign rvfi_csr_mstatush_rmask          = '1;
  assign rvfi_csr_mstatush_wdata          = rvfi_csr_wdata.mstatush;
  assign rvfi_csr_mstatush_wmask          = rvfi_csr_wmask.mstatush;
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
  assign rvfi_csr_mtvt_rdata              = rvfi_csr_rdata.mtvt;
  assign rvfi_csr_mtvt_rmask              = '1;
  assign rvfi_csr_mtvt_wdata              = rvfi_csr_wdata.mtvt;
  assign rvfi_csr_mtvt_wmask              = rvfi_csr_wmask.mtvt;
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
  assign rvfi_csr_mnxti_rmask             = '1;
  assign rvfi_csr_mnxti_rdata             = rvfi_csr_rdata.mnxti;
  assign rvfi_csr_mnxti_wmask             = rvfi_csr_wmask.mnxti;
  assign rvfi_csr_mnxti_wdata             = rvfi_csr_wdata.mnxti;
  assign rvfi_csr_mintstatus_rdata        = rvfi_csr_rdata.mintstatus;
  assign rvfi_csr_mintstatus_rmask        = '1;
  assign rvfi_csr_mintstatus_wdata        = rvfi_csr_wdata.mintstatus;
  assign rvfi_csr_mintstatus_wmask        = rvfi_csr_wmask.mintstatus;
  assign rvfi_csr_mintthresh_rdata        = rvfi_csr_rdata.mintthresh;
  assign rvfi_csr_mintthresh_rmask        = '1;
  assign rvfi_csr_mintthresh_wdata        = rvfi_csr_wdata.mintthresh;
  assign rvfi_csr_mintthresh_wmask        = rvfi_csr_wmask.mintthresh;
  assign rvfi_csr_mscratchcsw_rdata       = rvfi_csr_rdata.mscratchcsw;
  assign rvfi_csr_mscratchcsw_rmask       = '1;
  assign rvfi_csr_mscratchcsw_wdata       = rvfi_csr_wdata.mscratchcsw;
  assign rvfi_csr_mscratchcsw_wmask       = rvfi_csr_wmask.mscratchcsw;
  assign rvfi_csr_mscratchcswl_rdata      = rvfi_csr_rdata.mscratchcswl;
  assign rvfi_csr_mscratchcswl_rmask      = '1;
  assign rvfi_csr_mscratchcswl_wdata      = rvfi_csr_wdata.mscratchcswl;
  assign rvfi_csr_mscratchcswl_wmask      = rvfi_csr_wmask.mscratchcswl;
  assign rvfi_csr_mclicbase_rdata         = rvfi_csr_rdata.mclicbase;
  assign rvfi_csr_mclicbase_rmask         = '1;
  assign rvfi_csr_mclicbase_wdata         = rvfi_csr_wdata.mclicbase;
  assign rvfi_csr_mclicbase_wmask         = rvfi_csr_wmask.mclicbase;
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
  assign rvfi_csr_tcontrol_rdata          = rvfi_csr_rdata.tcontrol;
  assign rvfi_csr_tcontrol_rmask          = '1;
  assign rvfi_csr_tcontrol_wdata          = rvfi_csr_wdata.tcontrol;
  assign rvfi_csr_tcontrol_wmask          = rvfi_csr_wmask.tcontrol;
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
  assign rvfi_csr_mcounteren_rdata        = rvfi_csr_rdata.mcounteren;
  assign rvfi_csr_mcounteren_rmask        = '1;
  assign rvfi_csr_mcounteren_wdata        = rvfi_csr_wdata.mcounteren;
  assign rvfi_csr_mcounteren_wmask        = rvfi_csr_wmask.mcounteren;
  assign rvfi_csr_pmpcfg_rdata            = rvfi_csr_rdata.pmpcfg;
  assign rvfi_csr_pmpcfg_rmask            = '1;
  assign rvfi_csr_pmpcfg_wdata            = rvfi_csr_wmask.pmpcfg;
  assign rvfi_csr_pmpcfg_wmask            = rvfi_csr_wdata.pmpcfg;
  assign rvfi_csr_pmpaddr_rdata           = rvfi_csr_rdata.pmpaddr;
  assign rvfi_csr_pmpaddr_rmask           = '1;
  assign rvfi_csr_pmpaddr_wdata           = rvfi_csr_wdata.pmpaddr;
  assign rvfi_csr_pmpaddr_wmask           = rvfi_csr_wmask.pmpaddr;
  assign rvfi_csr_mseccfg_rdata           = rvfi_csr_rdata.mseccfg;
  assign rvfi_csr_mseccfg_rmask           = '1;
  assign rvfi_csr_mseccfg_wdata           = rvfi_csr_wdata.mseccfg;
  assign rvfi_csr_mseccfg_wmask           = rvfi_csr_wmask.mseccfg;
  assign rvfi_csr_mseccfgh_rdata          = rvfi_csr_rdata.mseccfgh;
  assign rvfi_csr_mseccfgh_rmask          = '1;
  assign rvfi_csr_mseccfgh_wdata          = rvfi_csr_wdata.mseccfgh;
  assign rvfi_csr_mseccfgh_wmask          = rvfi_csr_wmask.mseccfgh;

endmodule // cv32e40x_rvfi

