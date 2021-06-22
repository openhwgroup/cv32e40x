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
//  `include "cv32e40x_id_stage_sva.sv" // todo: why is this excluded (there is no instance of these assertions)
  `include "cv32e40x_ex_stage_sva.sv"
  `include "cv32e40x_wb_stage_sva.sv"
  `include "cv32e40x_load_store_unit_sva.sv"
  `include "cv32e40x_mpu_sva.sv"
  `include "cv32e40x_mult_sva.sv"
  `include "cv32e40x_prefetcher_sva.sv"
  `include "cv32e40x_prefetch_unit_sva.sv"
  `include "cv32e40x_sleep_unit_sva.sv"
`endif

`include "cv32e40x_core_log.sv"
`include "cv32e40x_dbg_helper.sv"

`ifdef RISCV_FORMAL
  `include "rvfi_macros.vh"
`endif

module cv32e40x_wrapper
  import cv32e40x_pkg::*;
#(
  parameter NUM_MHPMCOUNTERS             =  1,
  parameter int unsigned PMA_NUM_REGIONS =  0,
  parameter pma_region_t PMA_CFG[(PMA_NUM_REGIONS ? (PMA_NUM_REGIONS-1) : 0):0] = '{default:PMA_R_DEFAULT}
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
  input  logic [31:0] hart_id_i,
  input  logic [31:0] dm_exception_addr_i,
  input logic [31:0]  nmi_addr_i,

  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  output logic [1:0]  instr_memtype_o,
  output logic [2:0]  instr_prot_o,
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
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,
  output logic [5:0]  data_atop_o,
  input  logic        data_exokay_i,

  // Interrupt inputs
  input  logic [31:0] irq_i,                    // CLINT interrupts + CLINT extension interrupts
  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

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

/* todo: re-enable ID stage assertions

  bind cv32e40x_id_stage:
    core_i.id_stage_i cv32e40x_id_stage_sva id_stage_sva
    (
      .*
    );
*/

  bind cv32e40x_ex_stage:
    core_i.ex_stage_i cv32e40x_ex_stage_sva ex_stage_sva
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
      dbg_help_i(.is_compressed(if_id_pipe_i.is_compressed),
                 .rf_re    (core_i.rf_re_id               ),
                 .rf_raddr (core_i.rf_raddr_id            ),
                 .rf_we    (core_i.id_stage_i.rf_we       ),
                 .rf_waddr (core_i.rf_waddr_id            ),
                 .illegal_insn (core_i.id_stage_i.illegal_insn       ),
                 .*);

  bind cv32e40x_mult:            core_i.ex_stage_i.mult_i           cv32e40x_mult_sva         mult_sva         (.*);

  bind cv32e40x_controller_fsm:
    core_i.controller_i.controller_fsm_i
      cv32e40x_controller_fsm_sva
        controller_fsm_sva   (
                              .lsu_outstanding_cnt (core_i.load_store_unit_i.cnt_q),
                              .rf_we_wb_i          (core_i.wb_stage_i.rf_we_wb_o  ),
                              .csr_op_i            (core_i.cs_registers_i.csr_op  ),
                              .*);
  bind cv32e40x_cs_registers:        core_i.cs_registers_i              cv32e40x_cs_registers_sva cs_registers_sva (.*);

  bind cv32e40x_load_store_unit:
    core_i.load_store_unit_i cv32e40x_load_store_unit_sva #(.DEPTH (DEPTH)) load_store_unit_sva (
      // The SVA's monitor modport can't connect to a master modport, so it is connected to the interface instance directly:
      .m_c_obi_data_if(core_i.m_c_obi_data_if),
      .*);

  bind cv32e40x_prefetch_unit:
    core_i.if_stage_i.prefetch_unit_i cv32e40x_prefetch_unit_sva prefetch_unit_sva (.*);

  bind cv32e40x_div:
    core_i.ex_stage_i.div_i cv32e40x_div_sva div_sva (.*);

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
                .id_stage_is_last                 (core_i.id_stage_i.is_last),
                .id_stage_id_valid                (core_i.id_stage_i.id_valid),
                .*);

bind cv32e40x_sleep_unit:
  core_i.sleep_unit_i cv32e40x_sleep_unit_sva
    sleep_unit_sva (// probed id_stage_i.controller_i signals
                    .ctrl_fsm_cs (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                    .ctrl_fsm_ns (core_i.controller_i.controller_fsm_i.ctrl_fsm_ns),
                    .*);

  bind cv32e40x_decoder: core_i.id_stage_i.decoder_i cv32e40x_decoder_sva 
    decoder_sva(.clk(core_i.id_stage_i.clk), 
                .rst_n(core_i.id_stage_i.rst_n),
                .*);

  // MPU assertions
  bind cv32e40x_mpu: 
    core_i.if_stage_i.mpu_i 
    cv32e40x_mpu_sva
      #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
        .PMA_CFG(PMA_CFG))
  mpu_if_sva(.*);

  // TODO: Reintroduce once LSU PMA support has been properly implemented in the controller
  /*
  bind cv32e40x_mpu:
    core_i.load_store_unit_i.mpu_i
    cv32e40x_mpu_sva
      #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
        .PMA_CFG(PMA_CFG))
  mpu_lsu_sva(.*);
  */
`endif //  `ifndef COREV_ASSERT_OFF
  
    cv32e40x_core_log
     #(
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    core_log_i(
          .clk_i              ( core_i.id_stage_i.clk              ),
          .is_decoding_i      ( core_i.ctrl_fsm.is_decoding        ),
          .illegal_insn_dec_i ( core_i.id_stage_i.illegal_insn     ),
          .hart_id_i          ( core_i.hart_id_i                   ),
          .pc_id_i            ( core_i.if_id_pipe.pc               )
      );

    cv32e40x_rvfi
      rvfi_i
        (.clk_i                    ( clk_i                                                                ),
         .rst_ni                   ( rst_ni                                                               ),

         .instr_id_valid_i         ( core_i.id_stage_i.id_valid                                           ),

         .wb_valid_i               (core_i.wb_stage_i.wb_valid                                            ),
         .instr_rdata_wb_i         ( core_i.wb_stage_i.ex_wb_pipe_i.instr.bus_resp.rdata                  ),

         .rs1_addr_id_i            ( core_i.register_file_wrapper_i.register_file_i.raddr_i[0]            ),
         .rs2_addr_id_i            ( core_i.register_file_wrapper_i.register_file_i.raddr_i[1]            ),
         .rs1_rdata_id_i           ( core_i.id_stage_i.operand_a_fw                                       ),
         .rs2_rdata_id_i           ( core_i.id_stage_i.operand_b_fw                                       ),

         .insn_mret_wb_i           ( core_i.wb_stage_i.ex_wb_pipe_i.mret_insn                             ),
         .insn_ebrk_wb_i           ( core_i.wb_stage_i.ex_wb_pipe_i.ebrk_insn                             ),
         .insn_ecall_wb_i          ( core_i.wb_stage_i.ex_wb_pipe_i.ecall_insn                            ),
         .insn_fencei_wb_i         ( core_i.wb_stage_i.ex_wb_pipe_i.fencei_insn                           ),
         .illegal_insn_wb_i        ( core_i.wb_stage_i.ex_wb_pipe_i.illegal_insn                          ),

         .pc_wb_i                  ( core_i.wb_stage_i.ex_wb_pipe_i.pc                                    ),
         .pc_if_i                  ( core_i.if_stage_i.pc_if_o                                            ),
         .jump_target_id_i         ( core_i.if_stage_i.jump_target_id_i                                   ),

         .pc_set_i                 ( core_i.if_stage_i.ctrl_fsm_i.pc_set                                  ),
         .pc_mux_i                 ( core_i.if_stage_i.ctrl_fsm_i.pc_mux                                  ),
         .exc_pc_mux_i             ( core_i.if_stage_i.ctrl_fsm_i.exc_pc_mux                              ),

         .lsu_en_id_i              ( core_i.id_stage_i.lsu_en                                             ),
         .lsu_type_id_i            ( core_i.id_stage_i.lsu_type                                           ),
         .lsu_we_id_i              ( core_i.id_stage_i.lsu_we                                             ),

         .insn_ebrk_ex_i           ( core_i.ex_stage_i.id_ex_pipe_i.ebrk_insn                             ),
         .insn_ecall_ex_i          ( core_i.ex_stage_i.id_ex_pipe_i.ecall_insn                            ),
         .insn_fencei_ex_i         ( core_i.ex_stage_i.id_ex_pipe_i.fencei_insn                           ),
         .lsu_en_ex_i              ( core_i.ex_stage_i.id_ex_pipe_i.lsu_en                                ),
         .insn_mret_ex_i           ( core_i.ex_stage_i.id_ex_pipe_i.mret_insn                             ),
         .illegal_insn_ex_i        ( core_i.ex_stage_i.id_ex_pipe_i.illegal_insn                          ),

         .instr_ex_ready_i         ( core_i.ex_stage_i.ex_ready_o                                         ),
         .instr_ex_valid_i         ( core_i.ex_stage_i.ex_valid_o                                         ),

         .branch_target_ex_i       ( core_i.if_stage_i.branch_target_ex_i                                 ),

         .lsu_en_wb_i              ( core_i.wb_stage_i.ex_wb_pipe_i.lsu_en                                ),
         .lsu_addr_ex_i            ( core_i.load_store_unit_i.trans.addr                                  ),
         .lsu_wdata_ex_i           ( core_i.load_store_unit_i.trans.wdata                                 ),
         .lsu_misaligned_ex_i      ( core_i.load_store_unit_i.id_ex_pipe_i.lsu_misaligned                 ),

         .rd_we_wb_i               ( core_i.wb_stage_i.rf_we_wb_o                                         ),
         .rd_addr_wb_i             ( core_i.wb_stage_i.rf_waddr_wb_o                                      ),
         .rd_wdata_wb_i            ( core_i.wb_stage_i.rf_wdata_wb_o                                      ),
         .lsu_rvalid_wb_i          ( core_i.load_store_unit_i.resp_valid                                  ),
         .lsu_rdata_wb_i           ( core_i.load_store_unit_i.lsu_rdata_1_o                               ),

         .exception_target_wb_i    ( core_i.if_stage_i.exc_pc                                             ),

         .mepc_target_wb_i         ( core_i.if_stage_i.mepc_i                                             ),

         // CSRs
         .csr_mstatus_n_i          ( core_i.cs_registers_i.mstatus_n                                      ),
         .csr_mstatus_q_i          ( core_i.cs_registers_i.mstatus_q                                      ),
         .csr_mstatus_we_i         ( core_i.cs_registers_i.mstatus_we                                     ),
         .csr_misa_i               ( core_i.cs_registers_i.MISA_VALUE                                     ),
         .csr_mie_q_i              ( core_i.cs_registers_i.mie_q                                          ),
         .csr_mie_n_i              ( core_i.cs_registers_i.mie_n                                          ),
         .csr_mie_we_i             ( core_i.cs_registers_i.mie_we                                         ),
         .csr_mtvec_n_i            ( core_i.cs_registers_i.mtvec_n                                        ),
         .csr_mtvec_q_i            ( core_i.cs_registers_i.mtvec_q                                        ),
         .csr_mtvec_we_i           ( core_i.cs_registers_i.mtvec_we                                       ),
         .csr_mcountinhibit_q_i    ( core_i.cs_registers_i.mcountinhibit_q                                ),
         .csr_mcountinhibit_n_i    ( core_i.cs_registers_i.mcountinhibit_n                                ),
         .csr_mcountinhibit_we_i   ( core_i.cs_registers_i.mcountinhibit_we                               ),
         .csr_mhpmevent_q_i        ( core_i.cs_registers_i.mhpmevent_q                                    ),
         .csr_mhpmevent_n_i        ( core_i.cs_registers_i.mhpmevent_n                                    ),
         .csr_mhpmevent_we_i       ( core_i.cs_registers_i.mhpmevent_we                                   ),
         .csr_mscratch_q_i         ( core_i.cs_registers_i.mscratch_q                                     ),
         .csr_mscratch_n_i         ( core_i.cs_registers_i.mscratch_n                                     ),
         .csr_mscratch_we_i        ( core_i.cs_registers_i.mscratch_we                                    ),
         .csr_mepc_q_i             ( core_i.cs_registers_i.mepc_q                                         ),
         .csr_mepc_n_i             ( core_i.cs_registers_i.mepc_n                                         ),
         .csr_mepc_we_i            ( core_i.cs_registers_i.mepc_we                                        ),
         .csr_mcause_q_i           ( core_i.cs_registers_i.mcause_q                                       ),
         .csr_mcause_n_i           ( core_i.cs_registers_i.mcause_n                                       ),
         .csr_mcause_we_i          ( core_i.cs_registers_i.mcause_we                                      ),
         .csr_mip_i                ( core_i.cs_registers_i.mip_i                                          ),
         .csr_tdata1_n_i           ( core_i.cs_registers_i.tmatch_control_n                               ),
         .csr_tdata1_q_i           ( core_i.cs_registers_i.tmatch_control_q                               ),
         .csr_tdata1_we_i          ( core_i.cs_registers_i.tmatch_control_we                              ),
         .csr_tdata2_n_i           ( core_i.cs_registers_i.tmatch_value_n                                 ),
         .csr_tdata2_q_i           ( core_i.cs_registers_i.tmatch_value_q                                 ),
         .csr_tdata2_we_i          ( core_i.cs_registers_i.tmatch_value_we                                ),
         .csr_tinfo_i              ( core_i.cs_registers_i.tinfo_types                                    ),
         .csr_dcsr_q_i             ( core_i.cs_registers_i.dcsr_q                                         ),
         .csr_dcsr_n_i             ( core_i.cs_registers_i.dcsr_n                                         ),
         .csr_dcsr_we_i            ( core_i.cs_registers_i.dcsr_we                                        ),
         .csr_debug_csr_save_i     ( core_i.cs_registers_i.ctrl_fsm_i.debug_csr_save                      ),
         .csr_dpc_q_i              ( core_i.cs_registers_i.dpc_q                                          ),
         .csr_dpc_n_i              ( core_i.cs_registers_i.dpc_n                                          ),
         .csr_dpc_we_i             ( core_i.cs_registers_i.dpc_we                                         ),
         .csr_dscratch0_q_i        ( core_i.cs_registers_i.dscratch0_q                                    ),
         .csr_dscratch0_n_i        ( core_i.cs_registers_i.dscratch0_n                                    ),
         .csr_dscratch0_we_i       ( core_i.cs_registers_i.dscratch0_we                                   ),
         .csr_dscratch1_q_i        ( core_i.cs_registers_i.dscratch1_q                                    ),
         .csr_dscratch1_n_i        ( core_i.cs_registers_i.dscratch1_n                                    ),
         .csr_dscratch1_we_i       ( core_i.cs_registers_i.dscratch1_we                                   ),
         .csr_mhpmcounter_q_i      ( core_i.cs_registers_i.mhpmcounter_q                                  ),
         .csr_mvendorid_i          ( {MVENDORID_BANK, MVENDORID_OFFSET}                                   ),
         .csr_marchid_i            ( MARCHID                                                              ),
         .csr_mhartid_i            ( core_i.cs_registers_i.hart_id_i                                      )

`ifdef RISCV_FORMAL
         ,`RVFI_CONN
`endif
         );


    // instantiate the core
    cv32e40x_core
        #(
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ),
          .PMA_NUM_REGIONS       ( PMA_NUM_REGIONS       ),
          .PMA_CFG               ( PMA_CFG               ))
    core_i (.*);

endmodule
