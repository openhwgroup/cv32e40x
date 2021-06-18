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
  parameter NUM_MHPMCOUNTERS             =  1,
  parameter LIB                          =  0,
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
  input  logic [31:0] nmi_addr_i,               // TODO use

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
  input logic         fencei_flush_ack_i,       // TODO use

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_havereset_o,
  output logic        debug_running_o,
  output logic        debug_halted_o,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_sleep_o
);
  
  // Unused parameters and signals (left in code for future design extensions)
  localparam A_EXTENSION         =  0;
  localparam N_PMP_ENTRIES       = 16;
  localparam USE_PMP             =  0;
  localparam b_ext_e B_EXT       = NONE;

  logic [31:0]       pc_if;             // Program counter in IF stage


  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id;
  logic [31:0] branch_target_ex;
  logic        branch_decision_ex;

  // Busy signals
  logic        if_busy;
  logic        lsu_busy;

  // LSU number of outstanding transactions
  logic [1:0]  lsu_cnt;

  // ID/EX pipeline
  id_ex_pipe_t id_ex_pipe;

  // EX/WB pipeline
  ex_wb_pipe_t ex_wb_pipe;

  // IF/ID pipeline
  if_id_pipe_t if_id_pipe;

  // Controller FSM outputs
  ctrl_fsm_t   ctrl_fsm;
  
  // Register File Write Back
  logic        rf_we_wb;
  rf_addr_t    rf_waddr_wb;
  logic [31:0] rf_wdata_wb;

  // Forwarding RF from EX
  logic        rf_we_ex;
  rf_addr_t    rf_waddr_ex;
  logic [31:0] rf_wdata_ex;

  // Register file signals from ID/decoder to controller
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_id;
  rf_addr_t    rf_raddr_id[REGFILE_NUM_READ_PORTS];
  rf_addr_t    rf_waddr_id;

  // Register file read data
  rf_data_t    regfile_rdata_id[REGFILE_NUM_READ_PORTS];

  // Register file write interface
  rf_addr_t    regfile_waddr_wb[REGFILE_NUM_WRITE_PORTS];
  rf_data_t    regfile_wdata_wb[REGFILE_NUM_WRITE_PORTS];
  logic        regfile_we_wb   [REGFILE_NUM_WRITE_PORTS];

  // Register file write enable for ALU insn in ID
  logic regfile_alu_we_id;

    // CSR control
  logic [23:0] mtvec_addr;
  logic [1:0]  mtvec_mode;

  logic [31:0] csr_rdata;
  logic        csr_valid;
  logic        csr_ready_ex;
  logic        csr_valid_ex;
  logic        csr_ready;

  PrivLvl_t    current_priv_lvl;

  // Load/store unit
  logic        lsu_misaligned;
  logic [31:0] lsu_rdata;
  logic        lsu_valid_0;
  logic        lsu_ready_ex;
  logic        lsu_valid_ex;
  logic        lsu_ready_0;
  logic        lsu_valid_1;
  logic        lsu_ready_wb;
  logic        lsu_valid_wb;
  logic        lsu_ready_1;

  // stall control from controller
  // TODO:OK: Merge to single stall signal for use in ID
  logic        misaligned_stall_ct;
  logic        jr_stall_ct;
  logic        load_stall_ct;
  logic        csr_stall_ct;
  logic        wfi_stall_ct;

  // Stage ready signals
  logic        if_ready;
  logic        id_ready;
  logic        ex_ready;
  logic        wb_ready;

  // Stage valid signals
  logic        if_valid;
  logic        ex_valid;

  // Interrupts
  logic        m_irq_enable; // interrupt_controller
  logic [31:0] mepc, dpc;    // from cs_registers
  logic [31:0] mie;          // from cs_registers 
  logic [31:0] mip;          // from cs_registers

  // Signal from IF to init mtvec at boot time
  logic        csr_mtvec_init_if;

  // debug mode and dcsr configuration
  // From cs_registers
  logic        debug_single_step;
  logic        debug_ebreakm;

  // trigger match detected in cs_registers (using ID timing)
  logic        debug_trigger_match_id;

  // Performance Counters
  // Currently from ID
  // TODO:OK: perf counter events should be moved to the controller, leaving as is for now
  logic        mhpmevent_minstret;
  logic        mhpmevent_load;
  logic        mhpmevent_store;
  logic        mhpmevent_jump;
  logic        mhpmevent_branch;
  logic        mhpmevent_branch_taken;
  logic        mhpmevent_compressed;
  logic        mhpmevent_jr_stall;
  logic        mhpmevent_imiss;
  logic        mhpmevent_ld_stall;
  logic        perf_imiss;

  // WB is writing back a LSU result
  logic        lsu_en_wb;

  // Controller <-> decoder 
  logic       deassert_we_ct;
  logic       mret_insn_id;
  logic       dret_insn_id;
  logic       csr_status_id;
  logic [1:0] ctrl_transfer_insn_id;
  logic [1:0] ctrl_transfer_insn_raw_id;
 
  logic        csr_en_id;
  csr_opcode_e csr_op_id;

  // Forward mux selectors controller -> id
  op_fw_mux_e  operand_a_fw_mux_sel_ct;
  op_fw_mux_e  operand_b_fw_mux_sel_ct;
  jalr_fw_mux_e  jalr_fw_mux_sel_ct;

  // irq signals
  // TODO:OK Should find a proper suffix for signals from interrupt_controller
  logic        irq_req_ctrl;
  logic [4:0]  irq_id_ctrl;
  logic        irq_wu_ctrl;

  // data bus error in WB
  logic        lsu_err_wb;
  logic [31:0] lsu_addr_wb;

  // Internal OBI interfaces
  if_c_obi #(.REQ_TYPE(obi_inst_req_t), .RESP_TYPE(obi_inst_resp_t))  m_c_obi_instr_if();
  if_c_obi #(.REQ_TYPE(obi_data_req_t), .RESP_TYPE(obi_data_resp_t))  m_c_obi_data_if();

  // Connect toplevel OBI signals to internal interfaces
  assign instr_req_o                         = m_c_obi_instr_if.s_req.req;
  assign instr_addr_o                        = m_c_obi_instr_if.req_payload.addr;
  assign instr_memtype_o                     = m_c_obi_instr_if.req_payload.memtype;
  assign instr_prot_o                        = m_c_obi_instr_if.req_payload.prot;
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
  assign data_wdata_o                        = m_c_obi_data_if.req_payload.wdata;
  assign data_atop_o                         = m_c_obi_data_if.req_payload.atop;
  assign m_c_obi_data_if.s_gnt.gnt           = data_gnt_i;
  assign m_c_obi_data_if.s_rvalid.rvalid     = data_rvalid_i;
  assign m_c_obi_data_if.resp_payload.rdata  = data_rdata_i;
  assign m_c_obi_data_if.resp_payload.err    = data_err_i;
  assign m_c_obi_data_if.resp_payload.exokay = data_exokay_i;

  assign fencei_flush_req_o = 1'b0; // TODO connect to controller when handshake is implemented

  assign debug_havereset_o = ctrl_fsm.debug_havereset;
  assign debug_halted_o    = ctrl_fsm.debug_halted;
  assign debug_running_o   = ctrl_fsm.debug_running;

  assign irq_ack_o         = ctrl_fsm.irq_ack;
  assign irq_id_o          = ctrl_fsm.irq_id;

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
    #(.LIB (LIB))
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
    #(.A_EXTENSION(A_EXTENSION),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  if_stage_i
  (
    .clk                 ( clk                       ),
    .rst_n               ( rst_ni                    ),

    // boot address
    .boot_addr_i         ( boot_addr_i[31:0]         ),
    .dm_exception_addr_i ( dm_exception_addr_i[31:0] ),

    // debug mode halt address
    .dm_halt_addr_i      ( dm_halt_addr_i[31:0]      ),

    // trap vector location
    .mtvec_addr          ( mtvec_addr                ),

    // instruction cache interface
    .m_c_obi_instr_if    ( m_c_obi_instr_if          ),

    // IF/ID pipeline
    .if_id_pipe_o        ( if_id_pipe                ),

    .ex_wb_pipe_i        ( ex_wb_pipe                ),
    
    .mepc_i              ( mepc                      ), // exception return address

    .dpc_i               ( dpc                       ), // debug return address

    .pc_if_o             ( pc_if                     ),

    .csr_mtvec_init_o    ( csr_mtvec_init_if         ),

    // Jump targets
    .jump_target_id_i    ( jump_target_id            ),
    .branch_target_ex_i  ( branch_target_ex          ),

    // pipeline stalls
    .id_ready_i          ( id_ready                  ),

    .if_valid_o          ( if_valid                  ),
    .if_ready_o          ( if_ready                  ),

    .if_busy_o           ( if_busy                   ),
    .perf_imiss_o        ( perf_imiss                ),

    .ctrl_fsm_i          ( ctrl_fsm                  )
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
    .USE_PMP                      ( USE_PMP                ),
    .A_EXTENSION                  ( A_EXTENSION            ),
    .B_EXT                        ( B_EXT                  )
  )
  id_stage_i
  (
    .clk                          ( clk                       ),     // Gated clock
    .clk_ungated_i                ( clk_i                     ),     // Ungated clock
    .rst_n                        ( rst_ni                    ),

    .deassert_we_i                ( deassert_we_ct            ),     // from controller bypass

    // Jumps and branches
    .branch_decision_i            ( branch_decision_ex        ),
    .jmp_target_o                 ( jump_target_id            ),

    // IF and ID control signals
    .id_ready_o                   ( id_ready                  ),
    .ex_ready_i                   ( ex_ready                  ),
    .wb_ready_i                   ( wb_ready                  ),
    .ex_valid_i                   ( ex_valid                  ),

    // IF/ID pipeline
    .if_id_pipe_i                 ( if_id_pipe                ),

    // ID/EX pipeline
    .id_ex_pipe_o                 ( id_ex_pipe                ),

    // From controller
    .ctrl_fsm_i                   ( ctrl_fsm                  ),

    // CSR ID/EX
    .current_priv_lvl_i           ( current_priv_lvl          ),

    // Debug Signals
    .debug_trigger_match_id_i     ( debug_trigger_match_id    ),       // from cs_registers (ID timing)

    // Register file write back and forwards
    .rf_we_ex_i                   ( rf_we_ex                  ),
    .rf_waddr_ex_i                ( rf_waddr_ex               ),
    .rf_wdata_ex_i                ( rf_wdata_ex               ),
    .rf_wdata_wb_i                ( rf_wdata_wb               ),
    .rf_wdata_wb_alu_i            ( ex_wb_pipe.rf_wdata       ),       // TODO:OK:Change to ex_wb_pipe

    // Performance Counters
    .mhpmevent_minstret_o         ( mhpmevent_minstret        ),
    .mhpmevent_load_o             ( mhpmevent_load            ),
    .mhpmevent_store_o            ( mhpmevent_store           ),
    .mhpmevent_jump_o             ( mhpmevent_jump            ),
    .mhpmevent_branch_o           ( mhpmevent_branch          ),
    .mhpmevent_branch_taken_o     ( mhpmevent_branch_taken    ),
    .mhpmevent_compressed_o       ( mhpmevent_compressed      ),
    .mhpmevent_jr_stall_o         ( mhpmevent_jr_stall        ),
    .mhpmevent_imiss_o            ( mhpmevent_imiss           ),
    .mhpmevent_ld_stall_o         ( mhpmevent_ld_stall        ),

    .perf_imiss_i                 ( perf_imiss                ),

    .lsu_en_wb_i                  ( lsu_en_wb                 ),

    .mret_insn_o                  ( mret_insn_id              ),
    .dret_insn_o                  ( dret_insn_id              ),
    .csr_status_o                 ( csr_status_id             ),

    .csr_en_o                     ( csr_en_id                 ),
    .csr_op_o                     ( csr_op_id                 ),

    .ctrl_transfer_insn_o         ( ctrl_transfer_insn_id),
    .ctrl_transfer_insn_raw_o     ( ctrl_transfer_insn_raw_id ),

    .rf_re_o                      ( rf_re_id                  ),
    .rf_raddr_o                   ( rf_raddr_id               ),
    .rf_waddr_o                   ( rf_waddr_id               ),

    .regfile_alu_we_id_o          ( regfile_alu_we_id         ),

    .operand_a_fw_mux_sel_i       ( operand_a_fw_mux_sel_ct   ),
    .operand_b_fw_mux_sel_i       ( operand_b_fw_mux_sel_ct   ),
    .jalr_fw_mux_sel_i            ( jalr_fw_mux_sel_ct        ),

    .misaligned_stall_i           ( misaligned_stall_ct       ),
    .jr_stall_i                   ( jr_stall_ct               ),
    .load_stall_i                 ( load_stall_ct             ),
    .csr_stall_i                  ( csr_stall_ct              ),
    .wfi_stall_i                  ( wfi_stall_ct              ),

    .regfile_rdata_i              ( regfile_rdata_id          )
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
    .csr_valid_i                ( csr_valid                    ),
    .csr_ready_o                ( csr_ready_ex                 ),
    .csr_valid_o                ( csr_valid_ex                 ),
    .csr_ready_i                ( csr_ready                    ),

    // Branch decision
    .branch_decision_o          ( branch_decision_ex           ),
    .branch_target_o            ( branch_target_ex             ),

    // Register file forwarding
    .rf_we_o                    ( rf_we_ex                     ),
    .rf_waddr_o                 ( rf_waddr_ex                  ),
    .rf_wdata_o                 ( rf_wdata_ex                  ),

    // LSU interface
    .lsu_valid_i                ( lsu_valid_0                  ),
    .lsu_ready_o                ( lsu_ready_ex                 ),
    .lsu_valid_o                ( lsu_valid_ex                 ),
    .lsu_ready_i                ( lsu_ready_0                  ),

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
    #(.A_EXTENSION(A_EXTENSION),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_ni             ),

    // From controller FSM
    .ctrl_fsm_i            ( ctrl_fsm           ),

    // Output to data memory
    .m_c_obi_data_if       ( m_c_obi_data_if    ),

    // ID/EX pipeline
    .id_ex_pipe_i          ( id_ex_pipe         ),

    .lsu_addr_wb_o         ( lsu_addr_wb        ),
    .lsu_err_wb_o          ( lsu_err_wb         ),
    .lsu_rdata_o           ( lsu_rdata          ), // todo: proper name
    .lsu_misaligned_o      ( lsu_misaligned     ), // todo: proper name

    // Control signals
    .cnt_o                 ( lsu_cnt            ), // Number of current outstanding transactions
    .busy_o                ( lsu_busy           ),

    // Handshakes
    .valid_0_i             ( lsu_valid_ex       ), // First LSU stage (EX)
    .ready_0_o             ( lsu_ready_0        ),
    .valid_0_o             ( lsu_valid_0        ),
    .ready_0_i             ( lsu_ready_ex       ),

    .valid_1_i             ( lsu_valid_wb       ), // Second LSU stage (WB)
    .ready_1_o             ( lsu_ready_1        ),
    .valid_1_o             ( lsu_valid_1        ),
    .ready_1_i             ( lsu_ready_wb       )
  );

  ////////////////////////////////////////////////////////////////////////////////////////
  // Write back stage                                                                   //
  ////////////////////////////////////////////////////////////////////////////////////////

  cv32e40x_wb_stage
  wb_stage_i
  (
    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe                   ),

    // From controller FSM
    .ctrl_fsm_i                 ( ctrl_fsm                     ),

    // LSU interface
    .lsu_rdata_i                ( lsu_rdata                    ),
    .lsu_valid_i                ( lsu_valid_1                  ),
    .lsu_ready_o                ( lsu_ready_wb                 ),
    .lsu_valid_o                ( lsu_valid_wb                 ),
    .lsu_ready_i                ( lsu_ready_1                  ),

    .lsu_en_wb_o                ( lsu_en_wb                    ),

    // Write back to register file
    .rf_we_wb_o                 ( rf_we_wb                     ),
    .rf_waddr_wb_o              ( rf_waddr_wb                  ),
    .rf_wdata_wb_o              ( rf_wdata_wb                  ),
  
    .wb_ready_o                 ( wb_ready                     )
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
    .A_EXTENSION      ( A_EXTENSION           ),
    .USE_PMP          ( USE_PMP               ),
    .N_PMP_ENTRIES    ( N_PMP_ENTRIES         ),
    .NUM_MHPMCOUNTERS ( NUM_MHPMCOUNTERS      )
  )
  cs_registers_i
  (
    .clk                        ( clk                    ),
    .rst_n                      ( rst_ni                 ),

    // Hart ID from outside
    .hart_id_i                  ( hart_id_i              ),

    .mtvec_addr_o               ( mtvec_addr             ),
    .mtvec_mode_o               ( mtvec_mode             ),

    // mtvec address
    .mtvec_addr_i               ( mtvec_addr_i[31:0]     ),
    .csr_mtvec_init_i           ( csr_mtvec_init_if      ),

    // IF/ID pipeline
    .if_id_pipe_i               ( if_id_pipe             ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe             ),

    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe             ),

    // From controller FSM
    .ctrl_fsm_i                 ( ctrl_fsm               ),

    // Interface to CSRs (SRAM like)
    .csr_rdata_o                ( csr_rdata              ),

    // Interrupt related control signals
    .mie_o                      ( mie                    ),
    .mip_i                      ( mip                    ),
    .m_irq_enable_o             ( m_irq_enable           ),
    .mepc_o                     ( mepc                   ),
    
    // debug
    .dpc_o                      ( dpc                    ),
    .debug_single_step_o        ( debug_single_step      ),
    .debug_ebreakm_o            ( debug_ebreakm          ),
    .debug_trigger_match_o      ( debug_trigger_match_id ),

    .priv_lvl_o                 ( current_priv_lvl       ),

    .pc_if_i                    ( pc_if                  ),

    // performance counter related signals
    .mhpmevent_minstret_i       ( mhpmevent_minstret     ),
    .mhpmevent_load_i           ( mhpmevent_load         ),
    .mhpmevent_store_i          ( mhpmevent_store        ),
    .mhpmevent_jump_i           ( mhpmevent_jump         ),
    .mhpmevent_branch_i         ( mhpmevent_branch       ),
    .mhpmevent_branch_taken_i   ( mhpmevent_branch_taken ),
    .mhpmevent_compressed_i     ( mhpmevent_compressed   ),
    .mhpmevent_jr_stall_i       ( mhpmevent_jr_stall     ),
    .mhpmevent_imiss_i          ( mhpmevent_imiss        ),
    .mhpmevent_ld_stall_i       ( mhpmevent_ld_stall     ),

    // Handshakes
    .valid_i                    ( csr_valid_ex           ),
    .ready_o                    ( csr_ready              ),
    .valid_o                    ( csr_valid              ),
    .ready_i                    ( csr_ready_ex           )
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
  controller_i
  (
    .clk                            ( clk                    ),         // Gated clock
    .clk_ungated_i                  ( clk_i                  ),         // Ungated clock
    .rst_n                          ( rst_ni                 ),

    .fetch_enable_i                 ( fetch_enable           ),

    // From ID/EX pipeline
    .id_ex_pipe_i                   ( id_ex_pipe             ),

    // From EX/WB pipeline
    .ex_wb_pipe_i                   ( ex_wb_pipe             ),

    // From bypass module
    .deassert_we_o                  ( deassert_we_ct         ),

    .csr_status_i                   ( csr_status_id          ),

    .if_valid_i                     ( if_valid               ),
    .if_ready_i                     ( if_ready               ),

    // from IF/ID pipeline
    .if_id_pipe_i                   ( if_id_pipe             ),
    .mret_id_i                      ( mret_insn_id           ),
    .dret_id_i                      ( dret_insn_id           ),
    .csr_en_id_i                    ( csr_en_id              ),
    .csr_op_id_i                    ( csr_op_id              ),
                                                                 
    // LSU
    .lsu_cnt_i                      ( lsu_cnt                ),
    .lsu_misaligned_i               ( lsu_misaligned         ),
    .lsu_addr_wb_i                  ( lsu_addr_wb            ),
    .lsu_en_wb_i                    ( lsu_en_wb              ),
    .lsu_err_wb_i                   ( lsu_err_wb             ),
  
    // jump/branch control
    .branch_decision_ex_i           ( branch_decision_ex     ),
    .ctrl_transfer_insn_i           ( ctrl_transfer_insn_id  ),
    .ctrl_transfer_insn_raw_i       ( ctrl_transfer_insn_raw_id ),

    // Interrupt signals
    .irq_wu_ctrl_i                  ( irq_wu_ctrl            ),
    .irq_req_ctrl_i                 ( irq_req_ctrl           ),
    .irq_id_ctrl_i                  ( irq_id_ctrl            ),
    .current_priv_lvl_i             ( current_priv_lvl       ), // TODO:OK: Needs bypass?
    
    // From CSR registers
    .mtvec_mode_i                   ( mtvec_mode             ), // TODO:OK: Bypass?

    // Debug signals
    .debug_req_i                    ( debug_req_i            ), 
    .debug_single_step_i            ( debug_single_step      ), // TODO:OK: Bypass?
    .debug_ebreakm_i                ( debug_ebreakm          ), // TODO:OK: Bypass?
    .debug_trigger_match_id_i       ( debug_trigger_match_id ),
    
    // Register File read, write back and forwards
    .rf_re_i                        ( rf_re_id               ),       
    .rf_raddr_i                     ( rf_raddr_id            ),
    .rf_waddr_i                     ( rf_waddr_id            ),
    .rf_we_ex_i                     ( rf_we_ex               ),
    .rf_waddr_ex_i                  ( rf_waddr_ex            ),
    .rf_we_wb_i                     ( rf_we_wb               ),
    .rf_waddr_wb_i                  ( rf_waddr_wb            ),

    // Write targets from ID
    .regfile_alu_we_id_i            ( regfile_alu_we_id      ),
   
    // Forwarding signals from bypass module
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel_ct),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel_ct),
    .jalr_fw_mux_sel_o              ( jalr_fw_mux_sel_ct     ),

    // Stall signals
    .misaligned_stall_o             ( misaligned_stall_ct    ),
    .jr_stall_o                     ( jr_stall_ct            ),
    .load_stall_o                   ( load_stall_ct          ),
    .csr_stall_o                    ( csr_stall_ct           ),
    .wfi_stall_o                    ( wfi_stall_ct           ),

    .id_ready_i                     ( id_ready               ),
    .ex_valid_i                     ( ex_valid               ),
    .wb_ready_i                     ( wb_ready               ),

    .data_req_i                     ( data_req_o             ),
    .data_rvalid_i                  ( data_rvalid_i          ),

    .ctrl_fsm_o                     ( ctrl_fsm               )
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
    .m_ie_i               ( m_irq_enable       ),
    .current_priv_lvl_i   ( current_priv_lvl   )
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
  assign regfile_we_wb[0]    = rf_we_wb;
  assign regfile_waddr_wb[0] = rf_waddr_wb;
  assign regfile_wdata_wb[0] = rf_wdata_wb;

  cv32e40x_register_file_wrapper
  register_file_wrapper_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_ni             ),

    // Read ports
    .raddr_i            ( rf_raddr_id        ),
    .rdata_o            ( regfile_rdata_id   ), // todo: get consistent naming

    // Write ports
    .waddr_i            ( regfile_waddr_wb      ),
    .wdata_i            ( regfile_wdata_wb      ),
    .we_i               ( regfile_we_wb         )
  );

endmodule
