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
  
  // Unused parameters and signals (left in code for future design extensions)
  localparam A_EXTENSION         =  0;
  localparam N_PMP_ENTRIES       = 16;
  localparam USE_PMP             =  0;          // if PULP_SECURE is 1, you can still not use the PMP

  logic              clear_instr_valid;
  logic              pc_set;

  pc_mux_e           pc_mux_id;         // Mux selector for next PC
  exc_pc_mux_e       exc_pc_mux_id; // Mux selector for exception PC
  logic [4:0]        m_exc_vec_pc_mux; // Mux selector for vectored IRQ PC

  logic [31:0]       pc_if;             // Program counter in IF stage

  // ID performance counter signals
  logic        is_decoding;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id;
  logic [31:0] branch_target_ex;
  logic        branch_decision;
  logic        branch_taken_ex; // ID->controller

  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // ID/EX pipeline
  id_ex_pipe_t id_ex_pipe;

  // EX/WB pipeline
  ex_wb_pipe_t ex_wb_pipe;

  // IF/ID pipeline
  if_id_pipe_t if_id_pipe;
  
  // Register Write Control
  rf_addr_t    regfile_waddr_fw_wb_o;        // From WB to ID
  logic        regfile_we_wb;

  // Register File Write Back
  logic        rf_we_wb;
  rf_addr_t    rf_waddr_wb;
  logic [31:0] rf_wdata_wb;

  // Forwarding RF from EX
  logic        rf_we_ex;
  rf_addr_t    rf_waddr_ex;
  logic [31:0] rf_wdata_ex;

  // Register file signals from ID/decoder to controller
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re;
  rf_addr_t    rf_raddr[REGFILE_NUM_READ_PORTS];
  rf_addr_t    rf_waddr;

  // Register file read data
  rf_data_t    regfile_rdata[REGFILE_NUM_READ_PORTS];

  // Register file write interface
  rf_addr_t    regfile_waddr[REGFILE_NUM_WRITE_PORTS];
  rf_data_t    regfile_wdata[REGFILE_NUM_WRITE_PORTS];
  logic        regfile_we   [REGFILE_NUM_WRITE_PORTS];

  logic regfile_alu_we_dec_o;

  // CSR control
  logic [23:0] mtvec_addr;
  logic [1:0]  mtvec_mode;

  logic [31:0] csr_rdata;
  PrivLvl_t    current_priv_lvl;

  // Load/store unit
  logic        lsu_misaligned;
  logic [31:0] lsu_rdata;
  logic        lsu_ready_ex;
  logic        lsu_ready_wb;

  // stall control
  logic        halt_if;
  logic        halt_id;
  logic        halt_ex;
  logic        halt_wb;
  logic        misaligned_stall;
  logic        jr_stall;
  logic        load_stall;
  logic        csr_stall;

  logic        id_ready;
  logic        ex_ready;

  logic        id_valid;
  logic        ex_valid;
  logic        wb_valid;


  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;    // Id stage asserts a req to instruction core interface

  // Interrupts
  logic        m_irq_enable;
  logic [31:0] mepc, dpc;
  logic [31:0] mie_bypass;
  logic [31:0] mip;

  logic        csr_save_cause;
  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_ex;
  logic        csr_save_wb;
  logic [5:0]  csr_cause;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_mtvec_init;

  // debug mode and dcsr configuration
  logic        debug_mode;
  logic [2:0]  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_trigger_match;

  // Performance Counters
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

  // Wake signal
  logic        wake_from_sleep;

  // WB is writing back an ALU result
  logic        data_req_wb;

  // Blocking update of data address in WB (in case of bus errors)
  logic        block_data_addr;

  // data bus error in WB
  logic        data_err_wb;
  logic [31:0] data_addr_wb;

  // Controller <-> decoder 
  logic       deassert_we;
  logic       illegal_insn;
  logic       ecall_insn;
  logic       mret_insn;
  logic       dret_insn;
  logic       wfi_insn;
  logic       ebrk_insn;
  logic       fencei_insn;
  logic       csr_status;
  logic [1:0] ctrl_transfer_insn;
  logic [1:0] ctrl_transfer_insn_raw;
  logic       debug_wfi_no_sleep;

  logic       csr_en_id;
  csr_opcode_e csr_op_id;

  // Forward mux selectors controller -> id
  op_fw_mux_e  operand_a_fw_mux_sel;
  op_fw_mux_e  operand_b_fw_mux_sel;
  jalr_fw_mux_e  jalr_fw_mux_sel;

  // irq signals
  logic        irq_req_ctrl;
  logic [4:0]  irq_id_ctrl;
  logic        irq_wu_ctrl;

  // kill signals
  logic        kill_if;
  logic        kill_id;
  logic        kill_ex;
  logic        kill_wb;


  // Internal OBI interfaces
  if_c_obi #(.REQ_TYPE(obi_inst_req_t), .RESP_TYPE(obi_inst_resp_t))  m_c_obi_instr_if();
  if_c_obi #(.REQ_TYPE(obi_data_req_t), .RESP_TYPE(obi_data_resp_t))  m_c_obi_data_if();

  // Connect toplevel OBI signals to internal interfaces
  assign instr_req_o                         = m_c_obi_instr_if.req;
  assign instr_addr_o                        = m_c_obi_instr_if.req_payload.addr;
  assign m_c_obi_instr_if.gnt                = instr_gnt_i;
  assign m_c_obi_instr_if.rvalid             = instr_rvalid_i;
  assign m_c_obi_instr_if.resp_payload.rdata = instr_rdata_i;
  assign m_c_obi_instr_if.resp_payload.err   = instr_err_i;
  
  assign data_req_o                          = m_c_obi_data_if.req;
  assign data_we_o                           = m_c_obi_data_if.req_payload.we;
  assign data_be_o                           = m_c_obi_data_if.req_payload.be;
  assign data_addr_o                         = m_c_obi_data_if.req_payload.addr;
  assign data_wdata_o                        = m_c_obi_data_if.req_payload.wdata;
  assign data_atop_o                         = m_c_obi_data_if.req_payload.atop;
  assign m_c_obi_data_if.gnt                 = data_gnt_i;
  assign m_c_obi_data_if.rvalid              = data_rvalid_i;
  assign m_c_obi_data_if.resp_payload.rdata  = data_rdata_i;
  assign m_c_obi_data_if.resp_payload.err    = data_err_i;
  assign m_c_obi_data_if.resp_payload.exokay = data_exokay_i;

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
    .ctrl_busy_i                ( ctrl_busy            ),
    .lsu_busy_i                 ( lsu_busy             ),
  
    // WFI wake
    .wake_from_sleep_i          ( wake_from_sleep      )
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
    #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  if_stage_i
  (
    .clk                 ( clk               ),
    .rst_n               ( rst_ni            ),

    // boot address
    .boot_addr_i         ( boot_addr_i[31:0] ),
    .dm_exception_addr_i ( dm_exception_addr_i[31:0] ),

    // debug mode halt address
    .dm_halt_addr_i      ( dm_halt_addr_i[31:0] ),

    // trap vector location
    .mtvec_addr          ( mtvec_addr        ),

    // instruction request control
    .req_i               ( instr_req_int     ),

    .kill_if_i           ( kill_if           ),

    // instruction cache interface
    .m_c_obi_instr_if    ( m_c_obi_instr_if   ),

    // IF/ID pipeline
    .if_id_pipe_o        ( if_id_pipe        ),

    .wb_pc_i             ( ex_wb_pipe.pc     ),
    // control signals
    .clear_instr_valid_i ( clear_instr_valid ),
    .pc_set_i            ( pc_set            ),

    .mepc_i              ( mepc              ), // exception return address

    .dpc_i               ( dpc               ), // debug return address

    .pc_mux_i            ( pc_mux_id         ), // sel for pc multiplexer
    .exc_pc_mux_i        ( exc_pc_mux_id     ),

    .pc_if_o             ( pc_if             ),

    .m_exc_vec_pc_mux_i  ( m_exc_vec_pc_mux  ),

    .csr_mtvec_init_o    ( csr_mtvec_init    ),

    // Jump targets
    .jump_target_id_i    ( jump_target_id    ),
    .branch_target_ex_i  ( branch_target_ex  ),

    // pipeline stalls
    .halt_if_i           ( halt_if           ),
    .id_ready_i          ( id_ready          ),

    .if_busy_o           ( if_busy           ),
    .perf_imiss_o        ( perf_imiss        )
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
    .A_EXTENSION                  ( A_EXTENSION            )
  )
  id_stage_i
  (
    .clk                          ( clk                  ),     // Gated clock
    .clk_ungated_i                ( clk_i                ),     // Ungated clock
    .rst_n                        ( rst_ni               ),

    .scan_cg_en_i                 ( scan_cg_en_i         ),

    .deassert_we_i                ( deassert_we          ),

    .kill_id_i                    ( kill_id              ),
    // Processor Enable
    .is_decoding_i                ( is_decoding          ),

    // Jumps and branches
    .branch_decision_i            ( branch_decision      ),
    .jmp_target_o                 ( jump_target_id       ),

    // IF and ID control signals
    .clear_instr_valid_o          ( clear_instr_valid    ),

    .id_ready_o                   ( id_ready             ),
    .ex_ready_i                   ( ex_ready             ),
    .wb_ready_i                   ( lsu_ready_wb         ),

    .id_valid_o                   ( id_valid             ),
    .ex_valid_i                   ( ex_valid             ),

    // IF/ID pipeline
    .if_id_pipe_i                 ( if_id_pipe           ),

    // ID/EX pipeline
    .id_ex_pipe_o                 ( id_ex_pipe           ),

    // CSR ID/EX
    .current_priv_lvl_i           ( current_priv_lvl     ),

    // Debug Signalf
    .debug_mode_i                 ( debug_mode           ),

    // Register file write back and forwards
    .rf_we_ex_i                   ( rf_we_ex             ),
    .rf_waddr_ex_i                ( rf_waddr_ex          ),
    .rf_wdata_ex_i                ( rf_wdata_ex          ),
    .rf_wdata_wb_i                ( rf_wdata_wb          ),
    .rf_wdata_wb_alu_i            ( ex_wb_pipe.rf_wdata  ),

    // Performance Counters
    .mhpmevent_minstret_o         ( mhpmevent_minstret   ),
    .mhpmevent_load_o             ( mhpmevent_load       ),
    .mhpmevent_store_o            ( mhpmevent_store      ),
    .mhpmevent_jump_o             ( mhpmevent_jump       ),
    .mhpmevent_branch_o           ( mhpmevent_branch     ),
    .mhpmevent_branch_taken_o     ( mhpmevent_branch_taken ),
    .mhpmevent_compressed_o       ( mhpmevent_compressed ),
    .mhpmevent_jr_stall_o         ( mhpmevent_jr_stall   ),
    .mhpmevent_imiss_o            ( mhpmevent_imiss      ),
    .mhpmevent_ld_stall_o         ( mhpmevent_ld_stall   ),

    .perf_imiss_i                 ( perf_imiss           ),

    .data_req_wb_i                ( data_req_wb          ),

    .illegal_insn_o               ( illegal_insn         ),
    .ebrk_insn_o                  ( ebrk_insn            ),
    .mret_insn_o                  ( mret_insn            ),
    .dret_insn_o                  ( dret_insn            ),
    .ecall_insn_o                 ( ecall_insn           ),
    .wfi_insn_o                   ( wfi_insn             ),
    .fencei_insn_o                ( fencei_insn          ),
    .csr_status_o                 ( csr_status           ),

    .csr_en_o                     ( csr_en_id            ),
    .csr_op_o                     ( csr_op_id            ),

    .branch_taken_ex_o            ( branch_taken_ex      ),

    .ctrl_transfer_insn_o         ( ctrl_transfer_insn   ),
    .ctrl_transfer_insn_raw_o     ( ctrl_transfer_insn_raw ),
    .debug_wfi_no_sleep_i         ( debug_wfi_no_sleep   ),

    .rf_re_o                      ( rf_re                ),
    .rf_raddr_o                   ( rf_raddr             ),
    .rf_waddr_o                   ( rf_waddr             ),

    .regfile_alu_we_dec_o         ( regfile_alu_we_dec   ),

    .operand_a_fw_mux_sel_i       ( operand_a_fw_mux_sel ),
    .operand_b_fw_mux_sel_i       ( operand_b_fw_mux_sel ),
    .jalr_fw_mux_sel_i            ( jalr_fw_mux_sel      ),

    .halt_id_i                    ( halt_id              ),
    .misaligned_stall_i           ( misaligned_stall     ),
    .jr_stall_i                   ( jr_stall             ),
    .load_stall_i                 ( load_stall           ),
    .csr_stall_i                  ( csr_stall            ),

    .regfile_rdata_i              ( regfile_rdata        )
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

    .kill_ex_i                  ( kill_ex                      ),
    .halt_ex_i                  ( halt_ex                      ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe                   ),

    // EX/WB pipeline
    .ex_wb_pipe_o               ( ex_wb_pipe                   ),

    // interface with CSRs
    .csr_rdata_i                ( csr_rdata                    ),

    // To IF: Branch decision
    .branch_decision_o          ( branch_decision              ),
    .branch_target_o            ( branch_target_ex             ),

    // Register file forwarding signals (to ID)
    .rf_we_ex_o                 ( rf_we_ex                     ),
    .rf_waddr_ex_o              ( rf_waddr_ex                  ),
    .rf_wdata_ex_o              ( rf_wdata_ex                  ),

    // stall control
    .lsu_ready_ex_i             ( lsu_ready_ex                 ),

    .ex_ready_o                 ( ex_ready                     ),
    .ex_valid_o                 ( ex_valid                     ),
    .wb_ready_i                 ( lsu_ready_wb                 )
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
    #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_ni             ),

    .halt_ex_i             ( halt_ex            ),
    .halt_wb_i             ( halt_wb            ),

    .kill_ex_i             ( kill_ex            ),
    //output to data memory
    .m_c_obi_data_if       ( m_c_obi_data_if    ),
    // ID/EX pipeline
    .id_ex_pipe_i          ( id_ex_pipe         ),

    .data_addr_wb_o        ( data_addr_wb       ),
    .data_err_wb_o         ( data_err_wb        ),

    .block_data_addr_i     ( block_data_addr    ),
   
    .lsu_rdata_o           ( lsu_rdata          ),
    .lsu_misaligned_o      ( lsu_misaligned     ),

    // control signals
    .lsu_ready_ex_o        ( lsu_ready_ex       ),
    .lsu_ready_wb_o        ( lsu_ready_wb       ),

    .busy_o                ( lsu_busy           )
  );

  ////////////////////////////////////////////////////////////////////////////////////////
  // Write back stage                                                                   //
  ////////////////////////////////////////////////////////////////////////////////////////

  cv32e40x_wb_stage
  wb_stage_i
  (
    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe                   ),
    .kill_wb_i                  ( kill_wb                      ),

    .lsu_rdata_i                ( lsu_rdata                    ),
    .csr_rdata_i                ( csr_rdata                    ),
    .lsu_ready_wb_i             ( lsu_ready_wb                 ),

    // Write back to register file
    .rf_we_wb_o                 ( rf_we_wb                     ),
    .rf_waddr_wb_o              ( rf_waddr_wb                  ),
    .rf_wdata_wb_o              ( rf_wdata_wb                  ),
  
    .wb_valid_o                 ( wb_valid                     ),

    .data_req_wb_o              ( data_req_wb                  )
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
    .csr_mtvec_init_i           ( csr_mtvec_init         ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe             ),

    // EX/WB pipeline
    .ex_wb_pipe_i               ( ex_wb_pipe             ),

    .kill_wb_i                  ( kill_wb                ),
    // Interface to CSRs (SRAM like)
    .csr_rdata_o                ( csr_rdata              ),

    // Interrupt related control signals
    .mie_bypass_o               ( mie_bypass             ),
    .mip_i                      ( mip                    ),
    .m_irq_enable_o             ( m_irq_enable           ),
    .mepc_o                     ( mepc                   ),
    
    // debug
    .debug_mode_i               ( debug_mode             ),
    .debug_cause_i              ( debug_cause            ),
    .debug_csr_save_i           ( debug_csr_save         ),
    .dpc_o                      ( dpc                    ),
    .debug_single_step_o        ( debug_single_step      ),
    .debug_ebreakm_o            ( debug_ebreakm          ),
    .debug_trigger_match_o      ( debug_trigger_match    ),

    .priv_lvl_o                 ( current_priv_lvl       ),

    .pc_if_i                    ( pc_if                  ),
    .pc_id_i                    ( if_id_pipe.pc          ),
    .pc_wb_i                    ( ex_wb_pipe.pc          ),

    .csr_save_if_i              ( csr_save_if            ),
    .csr_save_id_i              ( csr_save_id            ),
    .csr_save_ex_i              ( csr_save_ex            ),
    .csr_save_wb_i              ( csr_save_wb            ),
    .csr_restore_mret_i         ( csr_restore_mret_id    ),
    .csr_restore_dret_i         ( csr_restore_dret_id    ),

    .csr_cause_i                ( csr_cause              ),
    .csr_save_cause_i           ( csr_save_cause         ),

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
    .mhpmevent_ld_stall_i       ( mhpmevent_ld_stall     )
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
    .ctrl_busy_o                    ( ctrl_busy              ),
    .is_decoding_o                  ( is_decoding            ),

    // decoder related signals
    .deassert_we_o                  ( deassert_we            ),

    .csr_status_i                   ( csr_status             ),

    // from IF/ID pipeline
    .if_id_pipe_i                   ( if_id_pipe             ),
    .mret_id_i                      ( mret_insn              ),
    //.dret_id_i                      ( dret_insn              ),
    .csr_en_id_i                    ( csr_en_id              ),
    .csr_op_id_i                    ( csr_op_id              ),

    // From ID/EX pipeline
    .id_ex_pipe_i                   ( id_ex_pipe             ),
    // From EX/WB pipeline
    .ex_wb_pipe_i                   ( ex_wb_pipe             ),
    // from prefetcher
    .instr_req_o                    ( instr_req_int          ),
                                                                 
    // to prefetcher                                             
    .pc_set_o                       ( pc_set                 ),
    .pc_mux_o                       ( pc_mux_id              ),
    .exc_pc_mux_o                   ( exc_pc_mux_id          ),
    .m_exc_vec_pc_mux_o             ( m_exc_vec_pc_mux       ),
    
    // LSU
    .data_misaligned_i              ( lsu_misaligned         ),

    .data_err_wb_i                  ( data_err_wb            ),
    .data_addr_wb_i                 ( data_addr_wb           ),
    .block_data_addr_o              ( block_data_addr        ),

    // jump/branch control
    .branch_taken_ex_i              ( branch_taken_ex        ),
    .ctrl_transfer_insn_i           ( ctrl_transfer_insn     ),
    .ctrl_transfer_insn_raw_i       ( ctrl_transfer_insn_raw ),

    // Interrupt signals
    .irq_wu_ctrl_i                  ( irq_wu_ctrl            ),
    .irq_req_ctrl_i                 ( irq_req_ctrl           ),
    .irq_id_ctrl_i                  ( irq_id_ctrl            ),
    .current_priv_lvl_i             ( current_priv_lvl       ), // TODO:OK: Needs bypass?
    .irq_ack_o                      ( irq_ack_o              ),
    .irq_id_o                       ( irq_id_o               ),
    
    // From CSR registers
    .mtvec_mode_i                   ( mtvec_mode             ), // TODO:OK: Bypass?

    // Debug Signal
    .debug_mode_o                   ( debug_mode             ),
    .debug_cause_o                  ( debug_cause            ),
    .debug_csr_save_o               ( debug_csr_save         ),
    .debug_req_i                    ( debug_req_i            ), 
    .debug_single_step_i            ( debug_single_step      ), // TODO:OK: Bypass?
    .debug_ebreakm_i                ( debug_ebreakm          ), // TODO:OK: Bypass?
    .debug_trigger_match_i          ( debug_trigger_match    ),
    .debug_wfi_no_sleep_o           ( debug_wfi_no_sleep     ),
    .debug_havereset_o              ( debug_havereset_o      ),
    .debug_running_o                ( debug_running_o        ),
    .debug_halted_o                 ( debug_halted_o         ),

    // Wakeup Signal
    .wake_from_sleep_o              ( wake_from_sleep        ),

    // CSR Controller Signals
    .csr_save_cause_o               ( csr_save_cause         ),
    .csr_cause_o                    ( csr_cause              ),
    .csr_save_if_o                  ( csr_save_if            ),
    .csr_save_id_o                  ( csr_save_id            ),
    .csr_save_ex_o                  ( csr_save_ex            ),
    .csr_save_wb_o                  ( csr_save_wb            ),
    .csr_restore_mret_id_o          ( csr_restore_mret_id    ),
    .csr_restore_dret_id_o          ( csr_restore_dret_id    ),

    // Register File read, write back and forwards
    .rf_re_i                        ( rf_re                  ),       
    .rf_raddr_i                     ( rf_raddr               ),
    .rf_waddr_i                     ( rf_waddr               ),
    .rf_we_ex_i                     ( rf_we_ex               ),
    .rf_waddr_ex_i                  ( rf_waddr_ex            ),
    .rf_we_wb_i                     ( rf_we_wb               ),
    .rf_waddr_wb_i                  ( rf_waddr_wb            ),

    // Write targets from ID
    .regfile_alu_we_id_i            ( regfile_alu_we_dec     ),
   
    // Forwarding signals
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel   ),
    .jalr_fw_mux_sel_o              ( jalr_fw_mux_sel        ),

    // Stall signals
    .halt_if_o                      ( halt_if                ),
    .halt_id_o                      ( halt_id                ),
    .halt_ex_o                      ( halt_ex                ),
    .halt_wb_o                      ( halt_wb                ),

    .kill_if_o                      ( kill_if                ),
    .kill_id_o                      ( kill_id                ),
    .kill_ex_o                      ( kill_ex                ),
    .kill_wb_o                      ( kill_wb                ),

    .misaligned_stall_o             ( misaligned_stall       ),
    .jr_stall_o                     ( jr_stall               ),
    .load_stall_o                   ( load_stall             ),
    .csr_stall_o                    ( csr_stall              ),

    .id_ready_i                     ( id_ready               ),
    .ex_valid_i                     ( ex_valid               ),
    .wb_ready_i                     ( lsu_ready_wb           ),
    .data_req_wb_i                  ( data_req_wb            ),

    .data_req_i                     ( data_req_o             )
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
    .mie_bypass_i         ( mie_bypass         ),
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
  assign regfile_we[0]    = rf_we_wb;
  assign regfile_waddr[0] = rf_waddr_wb;
  assign regfile_wdata[0] = rf_wdata_wb;

  cv32e40x_register_file_wrapper
  register_file_wrapper_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_ni             ),

    // Read ports
    .raddr_i            ( rf_raddr           ),
    .rdata_o            ( regfile_rdata      ),

    // Write ports
    .waddr_i            ( regfile_waddr      ),
    .wdata_i            ( regfile_wdata      ),
    .we_i               ( regfile_we         )
  );

endmodule
