// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a cv32e40x, containing cv32e40x, and tracer
// Contributor: Davide Schiavone <davide@openhwgroup.org>

`ifdef CV32E40P_ASSERT_ON
  `include "cv32e40x_prefetch_controller_sva.sv"
`endif

`include "cv32e40x_core_log.sv"

`ifdef CV32E40P_APU_TRACE
  `include "cv32e40x_apu_tracer.sv"
`endif

`ifdef CV32E40P_TRACE_EXECUTION
  `include "cv32e40x_tracer.sv"
`endif

module cv32e40x_wrapper
#(
  parameter NUM_MHPMCOUNTERS    =  1
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        pulp_clock_en_i,                  // PULP clock enable (only used if PULP_CLUSTER = 1)
  input  logic        scan_cg_en_i,                     // Enable all clock gates for testing

  // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [31:0] mtvec_addr_i,
  input  logic [31:0] dm_halt_addr_i,
  input  logic [31:0] hart_id_i,
  input  logic [31:0] dm_exception_addr_i,

  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,
  output logic [5:0]  data_atop_o,
  input  logic        data_exokay_i,

  // Interrupt inputs
  input  logic [31:0] irq_i,                    // CLINT interrupts + CLINT extension interrupts
  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_havereset_o,
  output logic        debug_running_o,
  output logic        debug_halted_o,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_sleep_o
);


`ifdef CV32E40P_ASSERT_ON

    // RTL Assertions
    bind cv32e40x_prefetch_controller:
      core_i.if_stage_i.prefetch_buffer_i.prefetch_controller_i
      cv32e40x_prefetch_controller_sva
      #(
          .DEPTH           ( DEPTH           ),
          .FIFO_ADDR_DEPTH ( FIFO_ADDR_DEPTH ))
      prefetch_controller_sva (
          .*);

`endif // CV32E40P_ASSERT_ON

    cv32e40x_core_log
     #(
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    core_log_i(
          .clk_i              ( core_i.id_stage_i.clk              ),
          .is_decoding_i      ( core_i.id_stage_i.is_decoding_o    ),
          .illegal_insn_dec_i ( core_i.id_stage_i.illegal_insn     ),
          .hart_id_i          ( core_i.hart_id_i                   ),
          .pc_id_i            ( core_i.if_id_pipe.pc               )
      );

`ifdef CV32E40P_APU_TRACE
    cv32e40x_apu_tracer apu_tracer_i(
      .clk_i        ( core_i.rst_ni                ),
      .rst_n        ( core_i.clk_i                 ),
      .hart_id_i    ( core_i.hart_id_i             ),
      .apu_valid_i  ( core_i.ex_stage_i.apu_valid  ),
      .apu_waddr_i  ( core_i.ex_stage_i.apu_waddr  ),
      .apu_result_i ( core_i.ex_stage_i.apu_result )
  );
`endif

`ifdef CV32E40P_TRACE_EXECUTION
    cv32e40x_tracer tracer_i(
      .clk_i          ( core_i.clk_i                                   ), // always-running clock for tracing
      .rst_n          ( core_i.rst_ni                                  ),

      .hart_id_i      ( core_i.hart_id_i                               ),

      .pc             ( core_i.id_stage_i.if_id_pipe_i.pc              ),
      .instr          ( core_i.id_stage_i.instr                        ),
      .controller_state_i ( core_i.id_stage_i.controller_i.ctrl_fsm_cs ),
      .compressed     ( core_i.id_stage_i.if_id_pipe_i.is_compressed   ),
      .id_valid       ( core_i.id_stage_i.id_valid_o                   ),
      .is_decoding    ( core_i.id_stage_i.is_decoding_o                ),
      .is_illegal     ( core_i.id_stage_i.illegal_insn                 ),
      .trigger_match  ( core_i.id_stage_i.trigger_match_i              ),
      .rs1_value      ( core_i.id_stage_i.operand_a_fw                 ),
      .rs2_value      ( core_i.id_stage_i.operand_b_fw                 ),
      .rs3_value      ( core_i.id_stage_i.alu_operand_c                ),
      .rs2_value_vec  ( core_i.id_stage_i.alu_operand_b                ),

      .rs1_is_fp('0),
      .rs2_is_fp('0),
      .rs3_is_fp('0),
      .rd_is_fp('0),

      .ex_valid       ( core_i.ex_valid                             ),
      .ex_reg_addr    ( core_i.rf_waddr_ex                          ),
      .ex_reg_we      ( core_i.rf_we_ex                             ),
      .ex_reg_wdata   ( core_i.rf_wdata_ex                          ),

      .ex_data_addr   ( core_i.data_addr_o                          ),
      .ex_data_req    ( core_i.data_req_o                           ),
      .ex_data_gnt    ( core_i.data_gnt_i                           ),
      .ex_data_we     ( core_i.data_we_o                            ),
      .ex_data_wdata  ( core_i.data_wdata_o                         ),
      .data_misaligned ( core_i.lsu_misaligned                      ),

      .ebrk_insn      ( core_i.id_stage_i.ebrk_insn                 ),
      .debug_mode     ( core_i.debug_mode                           ),
      .ebrk_force_debug_mode ( core_i.id_stage_i.controller_i.ebrk_force_debug_mode ),

      .wb_bypass      ( core_i.ex_stage_i.id_ex_pipe_i.branch_in_ex ),

      .wb_valid       ( core_i.wb_valid                             ),
      .wb_reg_addr    ( core_i.regfile_waddr_fw_wb_o                ),
      .wb_reg_we      ( core_i.regfile_we_wb                        ),
      .wb_reg_wdata   ( core_i.regfile_wdata                        ),

      .imm_u_type     ( core_i.id_stage_i.imm_u_type                ),
      .imm_uj_type    ( core_i.id_stage_i.imm_uj_type               ),
      .imm_i_type     ( core_i.id_stage_i.imm_i_type                ),
      .imm_z_type     ( core_i.id_stage_i.imm_z_type                ),
      .imm_s_type     ( core_i.id_stage_i.imm_s_type                ),
      .imm_sb_type    ( core_i.id_stage_i.imm_sb_type               ),
      .imm_clip_type  ( core_i.id_stage_i.instr[11:7]               )
    );
`endif

    // instantiate the core
    cv32e40x_core
        #(
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    core_i (.*);



endmodule
