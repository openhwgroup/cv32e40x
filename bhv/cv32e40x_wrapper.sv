// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a cv32e40x, containing cv32e40x and RVFI
// Contributors: Davide Schiavone <davide@openhwgroup.org>
//               Halfdan Bechmann <halfdan.behcmann@silabs.com>

`ifndef COREV_ASSERT_OFF
  `include "cv32e40x_alignment_buffer_sva.sv"
  `include "cv32e40x_controller_fsm_sva.sv"
  `include "cv32e40x_core_sva.sv"
  `include "cv32e40x_cs_registers_sva.sv"
  `include "cv32e40x_decoder_sva.sv"
  `include "cv32e40x_div_sva.sv"
  `include "cv32e40x_if_stage_sva.sv"
  `include "cv32e40x_id_stage_sva.sv"
  `include "cv32e40x_ex_stage_sva.sv"
  `include "cv32e40x_wb_stage_sva.sv"
  `include "cv32e40x_load_store_unit_sva.sv"
  `include "cv32e40x_write_buffer_sva.sv"
  `include "cv32e40x_lsu_response_filter_sva.sv"
  `include "cv32e40x_mpu_sva.sv"
  `include "cv32e40x_mult_sva.sv"
  `include "cv32e40x_prefetcher_sva.sv"
  `include "cv32e40x_prefetch_unit_sva.sv"
  `include "cv32e40x_sleep_unit_sva.sv"
  `include "cv32e40x_rvfi_sva.sv"
`endif

`include "cv32e40x_wrapper.vh"
`include "cv32e40x_core_log.sv"
`include "cv32e40x_dbg_helper.sv"

`ifdef RISCV_FORMAL
  `include "rvfi_macros.vh"
`endif

module cv32e40x_wrapper
  import cv32e40x_pkg::*;
#(
  parameter              LIB                          = 0,
  parameter rv32_e       RV32                         = RV32I,
  parameter bit          A_EXT                        = 0,
  parameter b_ext_e      B_EXT                        = B_NONE,
  parameter m_ext_e      M_EXT                        = M,
  parameter bit          X_EXT                        = 0,
  parameter int          X_NUM_RS                     = 2,
  parameter int          X_ID_WIDTH                   = 4,
  parameter int          X_MEM_WIDTH                  = 32,
  parameter int          X_RFR_WIDTH                  = 32,
  parameter int          X_RFW_WIDTH                  = 32,
  parameter logic [31:0] X_MISA                       = 32'h00000000,
  parameter logic [1:0]  X_ECS_XS                     = 2'b00,
  parameter bit          ZC_EXT                       = 0,
  parameter int          NUM_MHPMCOUNTERS             = 1,
  parameter bit          SMCLIC                       = 0,
  parameter int          DBG_NUM_TRIGGERS             = 1,
  parameter int          PMA_NUM_REGIONS              = 0,
  parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT}
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        scan_cg_en_i,                     // Enable all clock gates for testing

  // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [31:0] mtvec_addr_i,
  input  logic [31:0] dm_halt_addr_i,
  input  logic [31:0] mhartid_i,
  input  logic [31:0] mimpid_i,
  input  logic [31:0] dm_exception_addr_i,
  input logic [31:0]  nmi_addr_i,

  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  output logic [1:0]  instr_memtype_o,
  output logic [2:0]  instr_prot_o,
  output logic        instr_dbg_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [1:0]  data_memtype_o,
  output logic [2:0]  data_prot_o,
  output logic        data_dbg_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,
  output logic [5:0]  data_atop_o,
  input  logic        data_exokay_i,

  // Cycle Count
  output logic [63:0] mcycle_o,

  // eXtension interface
  if_xif.cpu_compressed xif_compressed_if,
  if_xif.cpu_issue      xif_issue_if,
  if_xif.cpu_commit     xif_commit_if,
  if_xif.cpu_mem        xif_mem_if,
  if_xif.cpu_mem_result xif_mem_result_if,
  if_xif.cpu_result     xif_result_if,

  // Interrupt inputs
  input  logic [31:0] irq_i,                    // CLINT interrupts + CLINT extension interrupts

  input  logic        clic_irq_i,
  input  logic [ 9:0] clic_irq_id_i,
  input  logic [ 7:0] clic_irq_il_i,
  input  logic [ 1:0] clic_irq_priv_i,
  input  logic        clic_irq_hv_i,
  output logic [ 9:0] clic_irq_id_o,
  output logic        clic_irq_mode_o,
  output logic        clic_irq_exit_o,

  // Fencei flush handshake
  output logic        fencei_flush_req_o,
  input logic         fencei_flush_ack_i,
  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_havereset_o,
  output logic        debug_running_o,
  output logic        debug_halted_o,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_sleep_o

`ifdef RISCV_FORMAL
  ,`RVFI_OUTPUTS
`endif
);


`ifndef COREV_ASSERT_OFF

  // RTL Assertions

  bind cv32e40x_if_stage:
    core_i.if_stage_i cv32e40x_if_stage_sva if_stage_sva
    (
      .m_c_obi_instr_if (core_i.m_c_obi_instr_if), // SVA monitor modport cannot connect to a master modport
      .*
    );

  bind cv32e40x_id_stage:
    core_i.id_stage_i cv32e40x_id_stage_sva id_stage_sva
    (
      .*
    );

  bind cv32e40x_ex_stage:
    core_i.ex_stage_i cv32e40x_ex_stage_sva #(.X_EXT(X_EXT)) ex_stage_sva
    (
      .*
    );

  bind cv32e40x_wb_stage:
    core_i.wb_stage_i cv32e40x_wb_stage_sva wb_stage_sva
    (
      .*
    );

  bind cv32e40x_id_stage:
    core_i.id_stage_i
    cv32e40x_dbg_helper
      dbg_help_i(.is_compressed (if_id_pipe_i.instr_meta.compressed),
                 .rf_re         (core_i.rf_re_id                   ),
                 .rf_raddr      (core_i.rf_raddr_id                ),
                 .rf_we         (core_i.id_stage_i.rf_we           ),
                 .rf_waddr      (core_i.id_stage_i.rf_waddr        ),
                 .illegal_insn  (core_i.id_stage_i.illegal_insn    ),
                 .*);

  generate
    if(M_EXT != M_NONE) begin: mul_sva
      bind cv32e40x_mult:
        core_i.ex_stage_i.mul.mult_i cv32e40x_mult_sva mult_sva (.*);
    end
  endgenerate

  bind cv32e40x_controller_fsm:
    core_i.controller_i.controller_fsm_i
      cv32e40x_controller_fsm_sva
        #(.X_EXT(X_EXT))
        controller_fsm_sva   (
                              .lsu_outstanding_cnt (core_i.load_store_unit_i.cnt_q),
                              .rf_we_wb_i          (core_i.wb_stage_i.rf_we_wb_o  ),
                              .csr_we_i            (core_i.cs_registers_i.csr_we_int  ),
                              .csr_illegal_i       (core_i.cs_registers_i.csr_illegal_o),
                              .xif_commit_kill     (core_i.xif_commit_if.commit.commit_kill),
                              .xif_commit_valid    (core_i.xif_commit_if.commit_valid),
                              .*);
  bind cv32e40x_cs_registers:        core_i.cs_registers_i              cv32e40x_cs_registers_sva cs_registers_sva (.*);

  bind cv32e40x_load_store_unit:
    core_i.load_store_unit_i cv32e40x_load_store_unit_sva #(.DEPTH (DEPTH)) load_store_unit_sva (
      // The SVA's monitor modport can't connect to a master modport, so it is connected to the interface instance directly:
      .m_c_obi_data_if(core_i.m_c_obi_data_if),
      .ex_wb_pipe_i   (core_i.ex_wb_pipe),
      .*);

  bind cv32e40x_prefetch_unit:
    core_i.if_stage_i.prefetch_unit_i cv32e40x_prefetch_unit_sva prefetch_unit_sva (.*);

  generate
    if(M_EXT == M) begin: div_sva
      bind cv32e40x_div:
        core_i.ex_stage_i.div.div_i cv32e40x_div_sva div_sva (.*);
    end
  endgenerate

  bind cv32e40x_alignment_buffer:
    core_i.if_stage_i.prefetch_unit_i.alignment_buffer_i
      cv32e40x_alignment_buffer_sva
        alignment_buffer_sva (.*);

  bind cv32e40x_prefetcher:
    core_i.if_stage_i.prefetch_unit_i.prefetcher_i
      cv32e40x_prefetcher_sva
        prefetcher_sva (.*);

  bind cv32e40x_core:
    core_i cv32e40x_core_sva
      #(.A_EXT(A_EXT),
        .PMA_NUM_REGIONS(PMA_NUM_REGIONS))
      core_sva (// probed cs_registers signals
                .cs_registers_mie_q               (core_i.cs_registers_i.mie_q),
                .cs_registers_mepc_n              (core_i.cs_registers_i.mepc_n),
                .cs_registers_mcause_q            (core_i.cs_registers_i.mcause_q),
                .cs_registers_mstatus_q           (core_i.cs_registers_i.mstatus_q),
                .cs_registers_csr_cause_i         (core_i.cs_registers_i.ctrl_fsm_i.csr_cause),
                .branch_taken_in_ex               (core_i.controller_i.controller_fsm_i.branch_taken_ex),
                .exc_cause                        (core_i.controller_i.controller_fsm_i.exc_cause),
                // probed controller signals
                .ctrl_fsm_ns  (core_i.controller_i.controller_fsm_i.ctrl_fsm_ns),
                .ctrl_debug_mode_n                (core_i.controller_i.controller_fsm_i.debug_mode_n),
                .ctrl_pending_debug               (core_i.controller_i.controller_fsm_i.pending_debug),
                .ctrl_debug_allowed               (core_i.controller_i.controller_fsm_i.debug_allowed),
                .id_stage_multi_cycle_id_stall    (core_i.id_stage_i.multi_cycle_id_stall),

                .id_stage_id_valid                (core_i.id_stage_i.id_valid_o),
                .irq_ack                          (core_i.irq_ack),
                .*);

  bind cv32e40x_sleep_unit:
    core_i.sleep_unit_i cv32e40x_sleep_unit_sva
      sleep_unit_sva (// probed id_stage_i.controller_i signals
                      .ctrl_fsm_cs (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                      .ctrl_fsm_ns (core_i.controller_i.controller_fsm_i.ctrl_fsm_ns),
                      .*);

  bind cv32e40x_decoder: core_i.id_stage_i.decoder_i cv32e40x_decoder_sva #(.A_EXT(A_EXT))
    decoder_sva(.clk   (core_i.id_stage_i.clk),
                .rst_n (core_i.id_stage_i.rst_n),
                .*);

  // MPU assertions
  bind cv32e40x_mpu:
    core_i.if_stage_i.mpu_i
    cv32e40x_mpu_sva
      #(.PMA_NUM_REGIONS                        (PMA_NUM_REGIONS),
        .PMA_CFG                                (PMA_CFG),
        .IS_INSTR_SIDE                          (1))
  mpu_if_sva(.pma_addr                          (pma_i.trans_addr_i),
             .pma_cfg                           (pma_i.pma_cfg),
             .obi_memtype                       (core_i.instr_memtype_o),
             .obi_addr                          (core_i.instr_addr_o),
             .obi_req                           (core_i.instr_req_o),
             .obi_gnt                           (core_i.instr_gnt_i),
             .write_buffer_state                (cv32e40x_pkg::WBUF_EMPTY),
             .write_buffer_valid_o              ('0),
             .write_buffer_txn_bufferable       ('0),
             .write_buffer_txn_cacheable        ('0),
             .*);

  bind cv32e40x_mpu:
    core_i.load_store_unit_i.mpu_i
    cv32e40x_mpu_sva
      #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
        .PMA_CFG(PMA_CFG),
        .IS_INSTR_SIDE(0))
  mpu_lsu_sva(.pma_addr(pma_i.trans_addr_i),
             .pma_cfg (pma_i.pma_cfg),
             .obi_memtype                       (core_i.data_memtype_o),
             .obi_addr                          (core_i.data_addr_o),
             .obi_req                           (core_i.data_req_o),
             .obi_gnt                           (core_i.data_gnt_i),
             .write_buffer_state                (core_i.load_store_unit_i.write_buffer_i.state),
             .write_buffer_valid_o              (core_i.load_store_unit_i.write_buffer_i.valid_o),
             .write_buffer_txn_bufferable       (core_i.load_store_unit_i.write_buffer_i.trans_o.memtype[0]),
             .write_buffer_txn_cacheable        (core_i.load_store_unit_i.write_buffer_i.trans_o.memtype[1]),
             .*);

  bind cv32e40x_lsu_response_filter :
    core_i.load_store_unit_i.response_filter_i
    cv32e40x_lsu_response_filter_sva #(.DEPTH(DEPTH))
      lsu_response_filter_sva (.*);

  bind cv32e40x_write_buffer:
    core_i.load_store_unit_i.write_buffer_i
    cv32e40x_write_buffer_sva
             #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
               .PMA_CFG(PMA_CFG))
      write_buffer_sva(.*);

  bind cv32e40x_rvfi:
    rvfi_i
    cv32e40x_rvfi_sva
      rvfi_sva(.irq_ack(core_i.irq_ack),
               .dbg_ack(core_i.dbg_ack),
               .ebreak_in_wb_i(core_i.controller_i.controller_fsm_i.ebreak_in_wb),
               .nmi_addr_i(core_i.nmi_addr_i),
               .*);

`endif //  `ifndef COREV_ASSERT_OFF

    cv32e40x_core_log
     #(
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    core_log_i(
          .clk_i              ( core_i.id_stage_i.clk              ),
          .ex_wb_pipe_i       ( core_i.ex_wb_pipe                  ),
          .mhartid_i          ( core_i.mhartid_i                   )

      );

    cv32e40x_rvfi
      rvfi_i
        (.clk_i                    ( clk_i                                                                ),
         .rst_ni                   ( rst_ni                                                               ),

         .if_valid_i               ( core_i.if_stage_i.if_valid_o                                         ),
         .id_valid_i               ( core_i.id_stage_i.id_valid_o                                         ),
         .id_ready_i               ( core_i.id_stage_i.id_ready_o                                         ),

         .wb_valid_i               ( core_i.wb_stage_i.wb_valid_o                                         ),
         .wb_ready_i               ( core_i.wb_stage_i.wb_ready_o                                         ),
         .instr_rdata_wb_i         ( core_i.wb_stage_i.ex_wb_pipe_i.instr.bus_resp.rdata                  ),
         .ebreak_in_wb_i           ( core_i.controller_i.controller_fsm_i.ebreak_in_wb                    ),

         .rs1_addr_id_i            ( core_i.register_file_wrapper_i.raddr_i[0]                            ),
         .rs2_addr_id_i            ( core_i.register_file_wrapper_i.raddr_i[1]                            ),
         .operand_a_fw_id_i        ( core_i.id_stage_i.operand_a_fw                                       ),
         .operand_b_fw_id_i        ( core_i.id_stage_i.operand_b_fw                                       ),

         .pc_if_i                  ( core_i.if_stage_i.pc_if_o                                            ),
         .pc_id_i                  ( core_i.id_stage_i.if_id_pipe_i.pc                                    ),
         .pc_wb_i                  ( core_i.wb_stage_i.ex_wb_pipe_i.pc                                    ),
         .sys_en_id_i              ( core_i.id_stage_i.sys_en_o                                           ),
         .sys_mret_insn_id_i       ( core_i.id_stage_i.sys_mret_insn_o                                    ),
         .jump_in_id_i             ( core_i.controller_i.controller_fsm_i.jump_in_id                      ),
         .jump_target_id_i         ( core_i.id_stage_i.jmp_target_o                                       ),
         .is_compressed_id_i       ( core_i.id_stage_i.if_id_pipe_i.instr_meta.compressed                 ),

         .lsu_en_id_i              ( core_i.id_stage_i.lsu_en                                             ),
         .lsu_size_id_i            ( core_i.id_stage_i.lsu_size                                           ),
         .lsu_we_id_i              ( core_i.id_stage_i.lsu_we                                             ),

         .branch_in_ex_i           ( core_i.controller_i.controller_fsm_i.branch_in_ex                    ),
         .lsu_en_ex_i              ( core_i.ex_stage_i.id_ex_pipe_i.lsu_en                                ),

         .instr_pmp_err_if_i       ( 1'b0                          /* PMP not implemented in cv32e40x */  ),
         .lsu_pmp_err_ex_i         ( 1'b0                          /* PMP not implemented in cv32e40x */  ),
         .lsu_pma_err_atomic_ex_i  ( core_i.load_store_unit_i.mpu_i.pma_i.atomic_access_i && // Todo: Consider making this a signal in the pma
                                    !core_i.load_store_unit_i.mpu_i.pma_i.pma_cfg_atomic                 ),

         .ex_ready_i               ( core_i.ex_stage_i.ex_ready_o                                         ),
         .ex_valid_i               ( core_i.ex_stage_i.ex_valid_o                                         ),

         .branch_target_ex_i       ( core_i.if_stage_i.branch_target_ex_i                                 ),

         .data_addr_ex_i           ( core_i.data_addr_o                                                   ),
         .data_wdata_ex_i          ( core_i.data_wdata_o                                                  ),
         .lsu_split_q_ex_i         ( core_i.load_store_unit_i.split_q                                     ),

         .rf_re_id_i               ( core_i.id_stage_i.rf_re_o                                            ),
         .rf_we_wb_i               ( core_i.wb_stage_i.rf_we_wb_o                                         ),
         .rf_addr_wb_i             ( core_i.wb_stage_i.rf_waddr_wb_o                                      ),
         .rf_wdata_wb_i            ( core_i.wb_stage_i.rf_wdata_wb_o                                      ),
         .lsu_rdata_wb_i           ( core_i.load_store_unit_i.lsu_rdata_1_o                               ),

         .branch_addr_n_i          ( core_i.if_stage_i.branch_addr_n                                      ),

         .priv_lvl_i               ( PRIV_LVL_M                       /* Not implemented in cv32e40x */   ),
         .ctrl_fsm_i               ( core_i.ctrl_fsm                                                      ),
         .pending_single_step_i    ( core_i.controller_i.controller_fsm_i.pending_single_step             ),
         .single_step_allowed_i    ( core_i.controller_i.controller_fsm_i.single_step_allowed             ),
         .nmi_pending_i            ( core_i.controller_i.controller_fsm_i.nmi_pending_q                   ),
         .nmi_is_store_i           ( core_i.controller_i.controller_fsm_i.nmi_is_store_q                  ),
         // CSRs
         .csr_jvt_n_i              ( core_i.cs_registers_i.jvt_n                                          ),
         .csr_jvt_q_i              ( core_i.cs_registers_i.jvt_q                                          ),
         .csr_jvt_we_i             ( core_i.cs_registers_i.jvt_we                                         ),
         .csr_mstatus_n_i          ( core_i.cs_registers_i.mstatus_n                                      ),
         .csr_mstatus_q_i          ( core_i.cs_registers_i.mstatus_q                                      ),
         .csr_mstatus_we_i         ( core_i.cs_registers_i.mstatus_we                                     ),
         .csr_misa_n_i             ( core_i.cs_registers_i.MISA_VALUE                                     ), // WARL
         .csr_misa_q_i             ( core_i.cs_registers_i.MISA_VALUE                                     ),
         .csr_misa_we_i            ( core_i.cs_registers_i.csr_we_int &&
                                     (core_i.cs_registers_i.csr_waddr == CSR_MISA)                        ),
         .csr_mie_q_i              ( core_i.cs_registers_i.mie_q                                          ),
         .csr_mie_n_i              ( core_i.cs_registers_i.mie_n                                          ),
         .csr_mie_we_i             ( core_i.cs_registers_i.mie_we                                         ),
         .csr_mtvec_n_i            ( core_i.cs_registers_i.mtvec_n                                        ),
         .csr_mtvec_q_i            ( core_i.cs_registers_i.mtvec_q                                        ),
         .csr_mtvec_we_i           ( core_i.cs_registers_i.mtvec_we                                       ),
         .csr_mtvt_n_i             ( core_i.cs_registers_i.mtvt_n                                         ),
         .csr_mtvt_q_i             ( core_i.cs_registers_i.mtvt_q                                         ),
         .csr_mtvt_we_i            ( core_i.cs_registers_i.mtvt_we                                        ),
         .csr_mcountinhibit_q_i    ( core_i.cs_registers_i.mcountinhibit_q                                ),
         .csr_mcountinhibit_n_i    ( core_i.cs_registers_i.mcountinhibit_n                                ),
         .csr_mcountinhibit_we_i   ( core_i.cs_registers_i.mcountinhibit_we                               ),
         .csr_mhpmevent_q_i        ( core_i.cs_registers_i.mhpmevent_q                                    ),
         .csr_mhpmevent_n_i        ( core_i.cs_registers_i.mhpmevent_n                                    ),
         .csr_mhpmevent_we_i       ( {31'h0, core_i.cs_registers_i.mhpmevent_we} << // todo:ok: Add write enable for each register
                                     core_i.cs_registers_i.csr_waddr[4:0] ),
         .csr_mscratch_q_i         ( core_i.cs_registers_i.mscratch_q                                     ),
         .csr_mscratch_n_i         ( core_i.cs_registers_i.mscratch_n                                     ),
         .csr_mscratch_we_i        ( core_i.cs_registers_i.mscratch_we                                    ),
         .csr_mepc_q_i             ( core_i.cs_registers_i.mepc_q                                         ),
         .csr_mepc_n_i             ( core_i.cs_registers_i.mepc_n                                         ),
         .csr_mepc_we_i            ( core_i.cs_registers_i.mepc_we                                        ),
         .csr_mcause_q_i           ( core_i.cs_registers_i.mcause_q                                       ),
         .csr_mcause_n_i           ( core_i.cs_registers_i.mcause_n                                       ),
         .csr_mcause_we_i          ( core_i.cs_registers_i.mcause_we                                      ),
         .csr_mip_n_i              ( core_i.cs_registers_i.mip_i                                          ),
         .csr_mip_q_i              ( core_i.cs_registers_i.mip_i                                          ),
         .csr_mip_we_i             ( core_i.cs_registers_i.csr_we_int &&
                                     (core_i.cs_registers_i.csr_waddr == CSR_MIP)                         ),
         .csr_mnxti_n_i            ( core_i.cs_registers_i.mnxti_n                                        ),
         .csr_mnxti_q_i            ( core_i.cs_registers_i.mnxti_q                                        ),
         .csr_mnxti_we_i           ( core_i.cs_registers_i.mnxti_we                                       ),
         .csr_mintstatus_n_i       ( core_i.cs_registers_i.mintstatus_n                                   ),
         .csr_mintstatus_q_i       ( core_i.cs_registers_i.mintstatus_q                                   ),
         .csr_mintstatus_we_i      ( core_i.cs_registers_i.mintstatus_we                                  ),
         .csr_mintthresh_n_i       ( core_i.cs_registers_i.mintthresh_n                                   ),
         .csr_mintthresh_q_i       ( core_i.cs_registers_i.mintthresh_q                                   ),
         .csr_mintthresh_we_i      ( core_i.cs_registers_i.mintthresh_we                                  ),
         .csr_mscratchcsw_n_i      ( core_i.cs_registers_i.mscratchcsw_n                                  ),
         .csr_mscratchcsw_q_i      ( core_i.cs_registers_i.mscratchcsw_q                                  ),
         .csr_mscratchcsw_we_i     ( core_i.cs_registers_i.mscratchcsw_we                                 ),
         .csr_mscratchcswl_n_i     ( core_i.cs_registers_i.mscratchcswl_n                                 ),
         .csr_mscratchcswl_q_i     ( core_i.cs_registers_i.mscratchcswl_q                                 ),
         .csr_mscratchcswl_we_i    ( core_i.cs_registers_i.mscratchcswl_we                                ),
         .csr_mclicbase_n_i        ( core_i.cs_registers_i.mclicbase_n                                    ),
         .csr_mclicbase_q_i        ( core_i.cs_registers_i.mclicbase_q                                    ),
         .csr_mclicbase_we_i       ( core_i.cs_registers_i.mclicbase_we                                   ),
         .csr_tdata1_n_i           ( core_i.cs_registers_i.tmatch_control_n                               ), // todo:ok:rename in RTL to use official CSR names from priv spec
         .csr_tdata1_q_i           ( core_i.cs_registers_i.tmatch_control_q                               ),
         .csr_tdata1_we_i          ( core_i.cs_registers_i.tmatch_control_we                              ),
         .csr_tdata2_n_i           ( core_i.cs_registers_i.tmatch_value_n                                 ), // todo:ok:rename in RTL to use official CSR names from priv spec
         .csr_tdata2_q_i           ( core_i.cs_registers_i.tmatch_value_q                                 ),
         .csr_tdata2_we_i          ( core_i.cs_registers_i.tmatch_value_we                                ),
         .csr_tinfo_n_i            ( {16'h0, core_i.cs_registers_i.tinfo_types}                           ),
         .csr_tinfo_q_i            ( {16'h0, core_i.cs_registers_i.tinfo_types}                           ),
         .csr_tinfo_we_i           ( core_i.cs_registers_i.csr_we_int &&
                                     (core_i.cs_registers_i.csr_waddr == CSR_TINFO)                       ),
         .csr_dcsr_q_i             ( core_i.cs_registers_i.dcsr_rdata                                     ),
         .csr_dcsr_n_i             ( core_i.cs_registers_i.dcsr_n                                         ),
         .csr_dcsr_we_i            ( core_i.cs_registers_i.dcsr_we                                        ),
         .csr_dpc_q_i              ( core_i.cs_registers_i.dpc_q                                          ),
         .csr_dpc_n_i              ( core_i.cs_registers_i.dpc_n                                          ),
         .csr_dpc_we_i             ( core_i.cs_registers_i.dpc_we                                         ),
         .csr_dscratch0_q_i        ( core_i.cs_registers_i.dscratch0_q                                    ),
         .csr_dscratch0_n_i        ( core_i.cs_registers_i.dscratch0_n                                    ),
         .csr_dscratch0_we_i       ( core_i.cs_registers_i.dscratch0_we                                   ),
         .csr_dscratch1_q_i        ( core_i.cs_registers_i.dscratch1_q                                    ),
         .csr_dscratch1_n_i        ( core_i.cs_registers_i.dscratch1_n                                    ),
         .csr_dscratch1_we_i       ( core_i.cs_registers_i.dscratch1_we                                   ),
         .csr_mhpmcounter_n_i      ( core_i.cs_registers_i.mhpmcounter_n                                  ),
         .csr_mhpmcounter_q_i      ( core_i.cs_registers_i.mhpmcounter_q                                  ),
         .csr_mhpmcounter_we_i     ( core_i.cs_registers_i.mhpmcounter_we                                 ),
         .csr_mvendorid_i          ( {MVENDORID_BANK, MVENDORID_OFFSET}                                   ),
         .csr_marchid_i            ( MARCHID                                                              ),
         .csr_mhartid_i            ( core_i.cs_registers_i.mhartid_i                                      ),
         .csr_mimpid_i             ( core_i.cs_registers_i.mimpid_i                                       ),
         // TODO Tie relevant signals below to RTL
         .csr_mstatush_n_i         ( '0                                                                   ),
         .csr_mstatush_q_i         ( '0                                                                   ),
         .csr_mstatush_we_i        ( '0                                                                   ),
         .csr_tcontrol_n_i         ( '0                                                                   ),
         .csr_tcontrol_q_i         ( '0                                                                   ),
         .csr_tcontrol_we_i        ( '0                                                                   ),
         .csr_mcounteren_n_i       ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mcounteren_q_i       ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mcounteren_we_i      ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_pmpcfg_n_i           ( '{16{8'h0}}                           /* Not supported in cv32e40x*/ ),
         .csr_pmpcfg_q_i           ( '{16{8'h0}}                           /* Not supported in cv32e40x*/ ),
         .csr_pmpcfg_we_i          ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_pmpaddr_n_i          ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_pmpaddr_q_i          ( '{16{32'h0}}                          /* Not supported in cv32e40x*/ ),
         .csr_pmpaddr_we_i         ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfg_n_i          ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfg_q_i          ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfg_we_i         ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfgh_n_i         ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfgh_q_i         ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mseccfgh_we_i        ( '0                                    /* Not supported in cv32e40x*/ ),
         .csr_mconfigptr_n_i       ( '0                                                                   ),
         .csr_mconfigptr_q_i       ( '0                                                                   ),
         .csr_mconfigptr_we_i      ( '0                                                                   )


`ifdef RISCV_FORMAL
         ,`RVFI_CONN
`else
         ,`RVFI_TIEOFF
`endif
         );


    // instantiate the core
    cv32e40x_core
        #(
          .LIB                   ( LIB                   ),
          .RV32                  ( RV32                  ),
          .A_EXT                 ( A_EXT                 ),
          .B_EXT                 ( B_EXT                 ),
          .M_EXT                 ( M_EXT                 ),
          .X_EXT                 ( X_EXT                 ),
          .X_NUM_RS              ( X_NUM_RS              ),
          .X_ID_WIDTH            ( X_ID_WIDTH            ),
          .X_MEM_WIDTH           ( X_MEM_WIDTH           ),
          .X_RFR_WIDTH           ( X_RFR_WIDTH           ),
          .X_RFW_WIDTH           ( X_RFW_WIDTH           ),
          .X_MISA                ( X_MISA                ),
          .X_ECS_XS              ( X_ECS_XS              ),
          .ZC_EXT                ( ZC_EXT                ),
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ),
          .SMCLIC                ( SMCLIC                ),
          .DBG_NUM_TRIGGERS      ( DBG_NUM_TRIGGERS      ),
          .PMA_NUM_REGIONS       ( PMA_NUM_REGIONS       ),
          .PMA_CFG               ( PMA_CFG               ))
    core_i (
            .xif_compressed_if(xif_compressed_if),
            .xif_issue_if(xif_issue_if),
            .xif_commit_if(xif_commit_if),
            .xif_mem_if(xif_mem_if),
            .xif_mem_result_if(xif_mem_result_if),
            .xif_result_if(xif_result_if),
            .*);

endmodule
