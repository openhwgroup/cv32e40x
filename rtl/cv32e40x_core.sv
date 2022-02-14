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
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_core import cv32e40x_pkg::*;
#(
  parameter              LIB                          = 0,
  parameter rv32_e       RV32                         = RV32I, // todo: Add support for RV32E
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
  parameter bit          ZC_EXT                       = 0, // todo: remove once fully implemented
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
  input  logic [31:0] nmi_addr_i,

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
  input  logic [11:0] clic_irq_id_i,
  input  logic [ 7:0] clic_irq_il_i,
  input  logic [ 1:0] clic_irq_priv_i,
  input  logic        clic_irq_hv_i,
  output logic [11:0] clic_irq_id_o,
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
);

  // Number of register file read ports
  // Core will only use two, but X_EXT may mandate 2 or 3
  localparam int unsigned REGFILE_NUM_READ_PORTS = X_EXT ? X_NUM_RS : 2;

  logic [31:0]       pc_if;             // Program counter in IF stage

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id;
  logic [31:0] branch_target_ex;
  logic        branch_decision_ex;

  // Busy signals
  logic        if_busy;
  logic        lsu_busy;
  logic        lsu_interruptible;

  // ID/EX pipeline
  id_ex_pipe_t id_ex_pipe;

  // EX/WB pipeline
  ex_wb_pipe_t ex_wb_pipe;

  // IF/ID pipeline
  if_id_pipe_t if_id_pipe;

  // Controller
  ctrl_byp_t   ctrl_byp;
  ctrl_fsm_t   ctrl_fsm;

  // Register File Write Back
  logic        rf_we_wb;
  rf_addr_t    rf_waddr_wb;
  logic [31:0] rf_wdata_wb;

  // Forwarding RF from EX
  logic [31:0] rf_wdata_ex;

  // Register file signals from ID/decoder to controller
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_id;
  rf_addr_t    rf_raddr_id[REGFILE_NUM_READ_PORTS];

  // Register file read data
  rf_data_t    rf_rdata_id[REGFILE_NUM_READ_PORTS];

  // Register file write interface
  rf_addr_t    rf_waddr[REGFILE_NUM_WRITE_PORTS];
  rf_data_t    rf_wdata[REGFILE_NUM_WRITE_PORTS];
  logic        rf_we   [REGFILE_NUM_WRITE_PORTS];

    // CSR control
  logic [23:0] mtvec_addr;
  logic [1:0]  mtvec_mode;

  logic [31:0] csr_rdata;
  logic csr_counter_read;

  // LSU
  logic        lsu_split_ex;
  mpu_status_e lsu_mpu_status_wb;
  logic [31:0] lsu_rdata_wb;
  logic [1:0]  lsu_err_wb;

  logic        lsu_valid_0;             // Handshake with EX
  logic        lsu_ready_ex;
  logic        lsu_valid_ex;
  logic        lsu_ready_0;

  logic        lsu_valid_1;             // Handshake with WB
  logic        lsu_ready_wb;
  logic        lsu_valid_wb;
  logic        lsu_ready_1;

  logic        data_stall_wb;

  // Stage ready signals
  logic        id_ready;
  logic        ex_ready;
  logic        wb_ready;

  // Stage valid signals
  logic        if_valid;
  logic        id_valid;
  logic        ex_valid;
  logic        wb_valid;

  // Interrupts
  logic        m_irq_enable; // interrupt_controller
  logic [31:0] mepc, dpc;    // from cs_registers
  logic [31:0] mie;          // from cs_registers
  logic [31:0] mip;          // from cs_registers

  // Signal from IF to init mtvec at boot time
  logic        csr_mtvec_init_if;

  // debug mode and dcsr configuration
  // From cs_registers
  dcsr_t       dcsr;

  // trigger match detected in cs_registers (using ID timing)
  logic        trigger_match_if;

  // Controller <-> decoder
  logic        alu_en_raw_id;
  logic        alu_jmp_id;
  logic        alu_jmpr_id;
  logic        sys_en_id;
  logic        sys_mret_insn_id;
  logic        csr_en_id;
  csr_opcode_e csr_op_id;
  logic        csr_illegal;

  // CSR illegal in EX due to offloading and pipeline accept
  logic        xif_csr_error_ex;

  // irq signals
  // TODO:AB Should find a proper suffix for signals from interrupt_controller
  logic        irq_req_ctrl;
  logic [4:0]  irq_id_ctrl;
  logic        irq_wu_ctrl;

  // Used (only) by verification environment
  logic        irq_ack;
  logic [4:0]  irq_id;
  logic        dbg_ack;

  // eXtension interface signals
  logic        xif_offloading_id;

  // Internal OBI interfaces
  if_c_obi #(.REQ_TYPE(obi_inst_req_t), .RESP_TYPE(obi_inst_resp_t))  m_c_obi_instr_if();
  if_c_obi #(.REQ_TYPE(obi_data_req_t), .RESP_TYPE(obi_data_resp_t))  m_c_obi_data_if();

  // Connect toplevel OBI signals to internal interfaces
  assign instr_req_o                         = m_c_obi_instr_if.s_req.req;
  assign instr_addr_o                        = m_c_obi_instr_if.req_payload.addr;
  assign instr_memtype_o                     = m_c_obi_instr_if.req_payload.memtype;
  assign instr_prot_o                        = m_c_obi_instr_if.req_payload.prot;
  assign instr_dbg_o                         = m_c_obi_instr_if.req_payload.dbg;
  assign m_c_obi_instr_if.s_gnt.gnt          = instr_gnt_i;
  assign m_c_obi_instr_if.s_rvalid.rvalid    = instr_rvalid_i;
  assign m_c_obi_instr_if.resp_payload.rdata = instr_rdata_i;
  assign m_c_obi_instr_if.resp_payload.err   = instr_err_i;

  assign data_req_o                          = m_c_obi_data_if.s_req.req;
  assign data_we_o                           = m_c_obi_data_if.req_payload.we;
  assign data_be_o                           = m_c_obi_data_if.req_payload.be;
  assign data_addr_o                         = m_c_obi_data_if.req_payload.addr;
  assign data_memtype_o                      = m_c_obi_data_if.req_payload.memtype;
  assign data_prot_o                         = m_c_obi_data_if.req_payload.prot;
  assign data_dbg_o                          = m_c_obi_data_if.req_payload.dbg;
  assign data_wdata_o                        = m_c_obi_data_if.req_payload.wdata;
  assign data_atop_o                         = m_c_obi_data_if.req_payload.atop;
  assign m_c_obi_data_if.s_gnt.gnt           = data_gnt_i;
  assign m_c_obi_data_if.s_rvalid.rvalid     = data_rvalid_i;
  assign m_c_obi_data_if.resp_payload.rdata  = data_rdata_i;
  assign m_c_obi_data_if.resp_payload.err    = data_err_i;
  assign m_c_obi_data_if.resp_payload.exokay = data_exokay_i;

  assign debug_havereset_o = ctrl_fsm.debug_havereset;
  assign debug_halted_o    = ctrl_fsm.debug_halted;
  assign debug_running_o   = ctrl_fsm.debug_running;

  // Used (only) by verification environment
  assign irq_ack = ctrl_fsm.irq_ack;
  assign irq_id  = ctrl_fsm.irq_id;
  assign dbg_ack = ctrl_fsm.dbg_ack;

  // todo: connect when CLIC is implemented
  assign clic_irq_id_o   = 12'h0;
  assign clic_irq_mode_o =  1'b0;
  assign clic_irq_exit_o =  1'b0;


  //////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ _            _      __  __                                                   _    //
  //  / ___| | ___   ___| | __ |  \/  | __ _ _ __   __ _  __ _  ___ _ __ ___   ___ _ __ | |_  //
  // | |   | |/ _ \ / __| |/ / | |\/| |/ _` | '_ \ / _` |/ _` |/ _ \ '_ ` _ \ / _ \ '_ \| __| //
  // | |___| | (_) | (__|   <  | |  | | (_| | | | | (_| | (_| |  __/ | | | | |  __/ | | | |_  //
  //  \____|_|\___/ \___|_|\_\ |_|  |_|\__,_|_| |_|\__,_|\__, |\___|_| |_| |_|\___|_| |_|\__| //
  //                                                     |___/                                //
  //////////////////////////////////////////////////////////////////////////////////////////////

  logic        clk;
  logic        fetch_enable;

  cv32e40x_sleep_unit
  #(
    .LIB                        ( LIB                  )
  )
  sleep_unit_i
  (
    // Clock, reset interface
    .clk_ungated_i              ( clk_i                ),       // Ungated clock
    .rst_n                      ( rst_ni               ),
    .clk_gated_o                ( clk                  ),       // Gated clock
    .scan_cg_en_i               ( scan_cg_en_i         ),

    // Core sleep
    .core_sleep_o               ( core_sleep_o         ),

    // Fetch enable
    .fetch_enable_i             ( fetch_enable_i       ),
    .fetch_enable_o             ( fetch_enable         ),

    // Core status
    .if_busy_i                  ( if_busy              ),
    .lsu_busy_i                 ( lsu_busy             ),

    // Inputs from controller (including busy)
    .ctrl_fsm_i                 ( ctrl_fsm             )
  );

  //////////////////////////////////////////////////
  //   ___ _____   ____ _____  _    ____ _____    //
  //  |_ _|  ___| / ___|_   _|/ \  / ___| ____|   //
  //   | || |_    \___ \ | | / _ \| |  _|  _|     //
  //   | ||  _|    ___) || |/ ___ \ |_| | |___    //
  //  |___|_|     |____/ |_/_/   \_\____|_____|   //
  //                                              //
  //////////////////////////////////////////////////
  cv32e40x_if_stage
  #(
    .A_EXT               ( A_EXT                    ),
    .X_EXT               ( X_EXT                    ),
    .X_ID_WIDTH          ( X_ID_WIDTH               ),
    .PMA_NUM_REGIONS     ( PMA_NUM_REGIONS          ),
    .PMA_CFG             ( PMA_CFG                  )
  )
  if_stage_i
  (
    .clk                 ( clk                      ),
    .rst_n               ( rst_ni                   ),

    .boot_addr_i         ( boot_addr_i              ), // Boot address
    .branch_target_ex_i  ( branch_target_ex         ), // Branch target address
    .dm_exception_addr_i ( dm_exception_addr_i      ), // Debug mode exception address
    .dm_halt_addr_i      ( dm_halt_addr_i           ), // Debug mode halt address
    .dpc_i               ( dpc                      ), // Debug PC (restore upon return from debug)
    .jump_target_id_i    ( jump_target_id           ), // Jump target address
    .mepc_i              ( mepc                     ), // Exception PC (restore upon return from exception/interrupt)
    .mtvec_addr_i        ( mtvec_addr               ), // Exception/interrupt address (MSBs only)
    .nmi_addr_i          ( nmi_addr_i               ), // NMI address

    .m_c_obi_instr_if    ( m_c_obi_instr_if         ), // Instruction bus interface

    .if_id_pipe_o        ( if_id_pipe               ),

    .ctrl_fsm_i          ( ctrl_fsm                 ),
    .trigger_match_i     ( trigger_match_if         ),

    .pc_if_o             ( pc_if                    ),
    .csr_mtvec_init_o    ( csr_mtvec_init_if        ),
    .if_busy_o           ( if_busy                  ),

    // Pipeline handshakes
    .if_valid_o          ( if_valid                 ),
    .id_ready_i          ( id_ready                 ),

    // eXtension interface
    .xif_compressed_if   ( xif_compressed_if        ),
    .xif_offloading_id_i ( xif_offloading_id        )
  );

  /////////////////////////////////////////////////
  //   ___ ____    ____ _____  _    ____ _____   //
  //  |_ _|  _ \  / ___|_   _|/ \  / ___| ____|  //
  //   | || | | | \___ \ | | / _ \| |  _|  _|    //
  //   | || |_| |  ___) || |/ ___ \ |_| | |___   //
  //  |___|____/  |____/ |_/_/   \_\____|_____|  //
  //                                             //
  /////////////////////////////////////////////////
  cv32e40x_id_stage
  #(
    .A_EXT                        ( A_EXT                     ),
    .B_EXT                        ( B_EXT                     ),
    .M_EXT                        ( M_EXT                     ),
    .X_EXT                        ( X_EXT                     ),
    .REGFILE_NUM_READ_PORTS       ( REGFILE_NUM_READ_PORTS    )
  )
  id_stage_i
  (
    .clk                          ( clk                       ),     // Gated clock
    .clk_ungated_i                ( clk_i                     ),     // Ungated clock
    .rst_n                        ( rst_ni                    ),

    // Jumps and branches
    .jmp_target_o                 ( jump_target_id            ),

    // IF/ID pipeline
    .if_id_pipe_i                 ( if_id_pipe                ),

    // ID/EX pipeline
    .id_ex_pipe_o                 ( id_ex_pipe                ),

    // EX/WB pipeline
    .ex_wb_pipe_i                 ( ex_wb_pipe                ),

    // Controller
    .ctrl_byp_i                   ( ctrl_byp                  ),
    .ctrl_fsm_i                   ( ctrl_fsm                  ),

    // Register file write back and forwards
    .rf_wdata_ex_i                ( rf_wdata_ex               ),
    .rf_wdata_wb_i                ( rf_wdata_wb               ),

    .alu_en_raw_o                 ( alu_en_raw_id             ),
    .alu_jmp_o                    ( alu_jmp_id                ),
    .alu_jmpr_o                   ( alu_jmpr_id               ),
    .sys_en_o                     ( sys_en_id                 ),
    .sys_mret_insn_o              ( sys_mret_insn_id          ),
    .csr_en_o                     ( csr_en_id                 ),
    .csr_op_o                     ( csr_op_id                 ),

    .rf_re_o                      ( rf_re_id                  ),
    .rf_raddr_o                   ( rf_raddr_id               ),
    .rf_rdata_i                   ( rf_rdata_id               ),

    // Pipeline handshakes
    .id_ready_o                   ( id_ready                  ),
    .id_valid_o                   ( id_valid                  ),
    .ex_ready_i                   ( ex_ready                  ),

    // eXtension interface
    .xif_issue_if                 ( xif_issue_if              ),
    .xif_offloading_o             ( xif_offloading_id         )
  );


  /////////////////////////////////////////////////////
  //   _______  __  ____ _____  _    ____ _____      //
  //  | ____\ \/ / / ___|_   _|/ \  / ___| ____|     //
  //  |  _|  \  /  \___ \ | | / _ \| |  _|  _|       //
  //  | |___ /  \   ___) || |/ ___ \ |_| | |___      //
  //  |_____/_/\_\ |____/ |_/_/   \_\____|_____|     //
  //                                                 //
  /////////////////////////////////////////////////////
  cv32e40x_ex_stage
  #(
    .X_EXT                      ( X_EXT                        ),
    .M_EXT                      ( M_EXT                        )
  )
  ex_stage_i
  (
    .clk                        ( clk                          ),
    .rst_n                      ( rst_ni                       ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe                   ),

    // EX/WB pipeline
    .ex_wb_pipe_o               ( ex_wb_pipe                   ),

    // From controller FSM
    .ctrl_fsm_i                 ( ctrl_fsm                     ),

    // CSR interface
    .csr_rdata_i                ( csr_rdata                    ),
    .csr_illegal_i              ( csr_illegal                  ),

    // Branch decision
    .branch_decision_o          ( branch_decision_ex           ),
    .branch_target_o            ( branch_target_ex             ),

    .xif_csr_error_o            ( xif_csr_error_ex             ),

    // Register file forwarding
    .rf_wdata_o                 ( rf_wdata_ex                  ),

    // LSU interface
    .lsu_valid_i                ( lsu_valid_0                  ),
    .lsu_ready_o                ( lsu_ready_ex                 ),
    .lsu_valid_o                ( lsu_valid_ex                 ),
    .lsu_ready_i                ( lsu_ready_0                  ),
    .lsu_split_i                ( lsu_split_ex                 ),

    // Pipeline handshakes
    .ex_ready_o                 ( ex_ready                     ),
    .ex_valid_o                 ( ex_valid                     ),
    .wb_ready_i                 ( wb_ready                     )
  );

  ////////////////////////////////////////////////////////////////////////////////////////
  //    _     ___    _    ____    ____ _____ ___  ____  _____   _   _ _   _ ___ _____   //
  //   | |   / _ \  / \  |  _ \  / ___|_   _/ _ \|  _ \| ____| | | | | \ | |_ _|_   _|  //
  //   | |  | | | |/ _ \ | | | | \___ \ | || | | | |_) |  _|   | | | |  \| || |  | |    //
  //   | |__| |_| / ___ \| |_| |  ___) || || |_| |  _ <| |___  | |_| | |\  || |  | |    //
  //   |_____\___/_/   \_\____/  |____/ |_| \___/|_| \_\_____|  \___/|_| \_|___| |_|    //
  //                                                                                    //
  ////////////////////////////////////////////////////////////////////////////////////////

  cv32e40x_load_store_unit
  #(
    .A_EXT                 (A_EXT               ),
    .PMA_NUM_REGIONS       (PMA_NUM_REGIONS     ),
    .PMA_CFG               (PMA_CFG             )
  )
  load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_ni             ),

    // ID/EX pipeline
    .id_ex_pipe_i          ( id_ex_pipe         ),

    // Controller
    .ctrl_fsm_i            ( ctrl_fsm           ),

    // Data OBI interface
    .m_c_obi_data_if       ( m_c_obi_data_if    ),

    // Control signals
    .busy_o                ( lsu_busy           ),
    .interruptible_o       ( lsu_interruptible  ),

    // Stage 0 outputs (EX)
    .lsu_split_0_o         ( lsu_split_ex       ),
    .lsu_mpu_status_1_o    ( lsu_mpu_status_wb  ),

    // Stage 1 outputs (WB)
    .lsu_err_1_o           ( lsu_err_wb         ), // To controller (has WB timing, but does not pass through WB stage)
    .lsu_rdata_1_o         ( lsu_rdata_wb       ),

    // Valid/ready
    .valid_0_i             ( lsu_valid_ex       ), // First LSU stage (EX)
    .ready_0_o             ( lsu_ready_0        ),
    .valid_0_o             ( lsu_valid_0        ),
    .ready_0_i             ( lsu_ready_ex       ),

    .valid_1_i             ( lsu_valid_wb       ), // Second LSU stage (WB)
    .ready_1_o             ( lsu_ready_1        ),
    .valid_1_o             ( lsu_valid_1        ),
    .ready_1_i             ( lsu_ready_wb       ),

    // eXtension interface
    .xif_mem_if            ( xif_mem_if         ),
    .xif_mem_result_if     ( xif_mem_result_if  )
  );

  ////////////////////////////////////////////////////////////////////////////////////////
  // Write back stage                                                                   //
  ////////////////////////////////////////////////////////////////////////////////////////

  cv32e40x_wb_stage
  wb_stage_i
  (
    .clk                        ( clk                          ), // Not used in RTL; only used by assertions
    .rst_n                      ( rst_ni                       ), // Not used in RTL; only used by assertions

    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe                   ),

    // Controller
    .ctrl_fsm_i                 ( ctrl_fsm                     ),

    // LSU
    .lsu_rdata_i                ( lsu_rdata_wb                 ),
    .lsu_mpu_status_i           ( lsu_mpu_status_wb            ),

    // Write back to register file
    .rf_we_wb_o                 ( rf_we_wb                     ),
    .rf_waddr_wb_o              ( rf_waddr_wb                  ),
    .rf_wdata_wb_o              ( rf_wdata_wb                  ),

    // LSU handshakes
    .lsu_valid_i                ( lsu_valid_1                  ),
    .lsu_ready_o                ( lsu_ready_wb                 ),
    .lsu_valid_o                ( lsu_valid_wb                 ),
    .lsu_ready_i                ( lsu_ready_1                  ),

    .data_stall_o               ( data_stall_wb                ),

    // Valid/ready
    .wb_ready_o                 ( wb_ready                     ),
    .wb_valid_o                 ( wb_valid                     ),

    // eXtension interface
    .xif_result_if              ( xif_result_if                )
  );

  //////////////////////////////////////
  //        ____ ____  ____           //
  //       / ___/ ___||  _ \ ___      //
  //      | |   \___ \| |_) / __|     //
  //      | |___ ___) |  _ <\__ \     //
  //       \____|____/|_| \_\___/     //
  //                                  //
  //   Control and Status Registers   //
  //////////////////////////////////////

  cv32e40x_cs_registers
  #(
    .A_EXT                      ( A_EXT                  ),
    .M_EXT                      ( M_EXT                  ),
    .X_EXT                      ( X_EXT                  ),
    .X_MISA                     ( X_MISA                 ),
    .X_ECS_XS                   ( X_ECS_XS               ),
    .ZC_EXT                     ( ZC_EXT                 ),
    .SMCLIC                     ( SMCLIC                 ),
    .DBG_NUM_TRIGGERS           ( DBG_NUM_TRIGGERS       ),
    .NUM_MHPMCOUNTERS           ( NUM_MHPMCOUNTERS       )
  )
  cs_registers_i
  (
    .clk                        ( clk                    ),
    .rst_n                      ( rst_ni                 ),

    // Hart ID from outside
    .mhartid_i                  ( mhartid_i             ),
    .mimpid_i                   ( mimpid_i              ),

    // Cycle Count
    .mcycle_o                   ( mcycle_o              ),

    .mtvec_addr_o               ( mtvec_addr             ),
    .mtvec_mode_o               ( mtvec_mode             ),

    // mtvec address
    .mtvec_addr_i               ( mtvec_addr_i[31:0]     ),
    .csr_mtvec_init_i           ( csr_mtvec_init_if      ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe             ),

    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe             ),

    // From controller FSM
    .ctrl_fsm_i                 ( ctrl_fsm               ),

    // Interface to CSRs (SRAM like)
    .csr_rdata_o                ( csr_rdata              ),

    .csr_illegal_o              (csr_illegal             ),

    // Raddr from first stage (EX)
    .csr_counter_read_o         ( csr_counter_read       ),

    // Interrupt related control signals
    .mie_o                      ( mie                    ),
    .mip_i                      ( mip                    ),
    .m_irq_enable_o             ( m_irq_enable           ),
    .mepc_o                     ( mepc                   ),

    // debug
    .dpc_o                      ( dpc                    ),
    .dcsr_o                     ( dcsr                   ),
    .trigger_match_o            ( trigger_match_if       ),

    .pc_if_i                    ( pc_if                  )
  );

  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////
  cv32e40x_controller
  #(
    .X_EXT                          ( X_EXT                  ),
    .REGFILE_NUM_READ_PORTS         ( REGFILE_NUM_READ_PORTS )
  )
  controller_i
  (
    .clk                            ( clk                    ),         // Gated clock
    .clk_ungated_i                  ( clk_i                  ),         // Ungated clock
    .rst_n                          ( rst_ni                 ),

    .fetch_enable_i                 ( fetch_enable           ),

    // From ID/EX pipeline
    .id_ex_pipe_i                   ( id_ex_pipe             ),

    .csr_counter_read_i             ( csr_counter_read       ),

    // From EX/WB pipeline
    .ex_wb_pipe_i                   ( ex_wb_pipe             ),

    .if_valid_i                     ( if_valid               ),
    .pc_if_i                        ( pc_if                  ),
    // from IF/ID pipeline
    .if_id_pipe_i                   ( if_id_pipe             ),

    .alu_en_raw_id_i                ( alu_en_raw_id          ),
    .alu_jmp_id_i                   ( alu_jmp_id             ),
    .alu_jmpr_id_i                  ( alu_jmpr_id            ),
    .sys_en_id_i                    ( sys_en_id              ),
    .sys_mret_id_i                  ( sys_mret_insn_id       ),
    .csr_en_id_i                    ( csr_en_id              ),
    .csr_op_id_i                    ( csr_op_id              ),

    // LSU
    .lsu_split_ex_i                 ( lsu_split_ex           ),
    .lsu_mpu_status_wb_i            ( lsu_mpu_status_wb      ),
    .data_stall_wb_i                ( data_stall_wb          ),
    .lsu_err_wb_i                   ( lsu_err_wb             ),
    .lsu_busy_i                     ( lsu_busy               ),
    .lsu_interruptible_i            ( lsu_interruptible      ),

    // jump/branch control
    .branch_decision_ex_i           ( branch_decision_ex     ),

    // Interrupt signals
    .irq_wu_ctrl_i                  ( irq_wu_ctrl            ),
    .irq_req_ctrl_i                 ( irq_req_ctrl           ),
    .irq_id_ctrl_i                  ( irq_id_ctrl            ),

    // From CSR registers
    .mtvec_mode_i                   ( mtvec_mode             ),

    // Debug signals
    .debug_req_i                    ( debug_req_i            ),
    .dcsr_i                         ( dcsr                   ),

    // Register File read, write back and forwards
    .rf_re_id_i                     ( rf_re_id               ),
    .rf_raddr_id_i                  ( rf_raddr_id            ),
    
    // Fencei flush handshake
    .fencei_flush_ack_i             ( fencei_flush_ack_i     ),
    .fencei_flush_req_o             ( fencei_flush_req_o     ),

    // Data OBI interface
    .m_c_obi_data_if                ( m_c_obi_data_if        ),

    .id_ready_i                     ( id_ready               ),
    .id_valid_i                     ( id_valid               ),
    .ex_ready_i                     ( ex_ready               ),
    .ex_valid_i                     ( ex_valid               ),
    .wb_ready_i                     ( wb_ready               ),
    .wb_valid_i                     ( wb_valid               ),

    .ctrl_byp_o                     ( ctrl_byp               ),
    .ctrl_fsm_o                     ( ctrl_fsm               ),

    // eXtension interface
    .xif_commit_if                  ( xif_commit_if          ),
    .xif_csr_error_i                ( xif_csr_error_ex       )
  );

  ////////////////////////////////////////////////////////////////////////
  //  _____      _       _____             _             _ _            //
  // |_   _|    | |     /  __ \           | |           | | |           //
  //   | | _ __ | |_    | /  \/ ___  _ __ | |_ _ __ ___ | | | ___ _ __  //
  //   | || '_ \| __|   | |    / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__| //
  //  _| || | | | |_ _  | \__/\ (_) | | | | |_| | | (_) | | |  __/ |    //
  //  \___/_| |_|\__(_)  \____/\___/|_| |_|\__|_|  \___/|_|_|\___|_|    //
  //                                                                    //
  ////////////////////////////////////////////////////////////////////////

  cv32e40x_int_controller
  int_controller_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_ni             ),

    // External interrupt lines
    .irq_i                ( irq_i              ),

    // To cv32e40x_controller
    .irq_req_ctrl_o       ( irq_req_ctrl       ),
    .irq_id_ctrl_o        ( irq_id_ctrl        ),
    .irq_wu_ctrl_o        ( irq_wu_ctrl        ),

    // To/from with cv32e40x_cs_registers
    .mie_i                ( mie                ),
    .mip_o                ( mip                ),
    .m_ie_i               ( m_irq_enable       )
  );

    /////////////////////////////////////////////////////////
  //  ____  _____ ____ ___ ____ _____ _____ ____  ____   //
  // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|  //
  // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \  //
  // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) | //
  // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/  //
  //                                                     //
  /////////////////////////////////////////////////////////

  // Connect register file write port(s) to regfile inputs
  assign rf_we[0]    = rf_we_wb;
  assign rf_waddr[0] = rf_waddr_wb;
  assign rf_wdata[0] = rf_wdata_wb;

  cv32e40x_register_file_wrapper
  #(
    .REGFILE_NUM_READ_PORTS       ( REGFILE_NUM_READ_PORTS    )
  )
  register_file_wrapper_i
  (
    .clk                ( clk         ),
    .rst_n              ( rst_ni      ),

    // Read ports
    .raddr_i            ( rf_raddr_id ),
    .rdata_o            ( rf_rdata_id ),

    // Write ports
    .waddr_i            ( rf_waddr    ),
    .wdata_i            ( rf_wdata    ),
    .we_i               ( rf_we       )
  );

endmodule
