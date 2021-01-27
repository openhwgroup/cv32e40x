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
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_core
#(
  parameter NUM_MHPMCOUNTERS    =  1
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
  if_obi_instr.master  m_obi_instr_if,

  // Data memory interface
  if_obi_data.master m_obi_data_if,

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
 
  import cv32e40x_pkg::*;
  
  
  // Unused parameters and signals (left in code for future design extensions)
  localparam A_EXTENSION         =  0;
  localparam N_PMP_ENTRIES       = 16;
  localparam USE_PMP             =  0;          // if PULP_SECURE is 1, you can still not use the PMP

  // Unused signals related to above unused parameters
  // Left in code (with their original _i, _o postfixes) for future design extensions;
  // these used to be former inputs/outputs of RI5CY

  logic [5:0]                     data_atop_o;  // atomic operation, only active if parameter `A_EXTENSION != 0`

  // IF/ID signals
  logic              instr_valid_id;
  logic [31:0]       instr_rdata_id;    // Instruction sampled inside IF stage
  logic              is_compressed_id;
  logic              illegal_c_insn_id;
  logic              is_fetch_failed_id;

  logic              clear_instr_valid;
  logic              pc_set;

  pc_mux_e           pc_mux_id;         // Mux selector for next PC
  exc_pc_mux_e       exc_pc_mux_id; // Mux selector for exception PC
  logic [4:0]        m_exc_vec_pc_mux_id; // Mux selector for vectored IRQ PC
  logic [4:0]        exc_cause;

  logic [31:0]       pc_if;             // Program counter in IF stage
  logic [31:0]       pc_id;             // Program counter in ID stage

  // ID performance counter signals
  logic        is_decoding;

  logic        data_misaligned;

  logic        mult_multicycle;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id, jump_target_ex;
  logic        branch_decision;

  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // ID/EX pipeline
  id_ex_pipe_t id_ex_pipe;

  // Register Write Control
  regfile_addr_t  regfile_waddr_fw_wb_o;        // From WB to ID
  logic        regfile_we_wb;
  logic [31:0] regfile_wdata;

  regfile_addr_t  regfile_alu_waddr_fw;
  logic           regfile_alu_we_fw;
  logic [31:0]    regfile_alu_wdata_fw;

  // CSR control
  logic [23:0] mtvec_addr;
  logic [1:0]  mtvec_mode;

  csr_opcode_e csr_op;
  csr_num_e    csr_addr;
  csr_num_e    csr_addr_int;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  PrivLvl_t    current_priv_lvl;

  logic [31:0] lsu_rdata;

  // stall control
  logic        halt_if;
  logic        id_ready;
  logic        ex_ready;

  logic        id_valid;
  logic        ex_valid;
  logic        wb_valid;

  logic        lsu_ready_ex;
  logic        lsu_ready_wb;

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
  logic        trigger_match;

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


  // Mux selector for vectored IRQ PC
  assign m_exc_vec_pc_mux_id = (mtvec_mode == 2'b0) ? 5'h0 : exc_cause;



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

    // instruction cache interface
    .m_obi_instr_if      ( m_obi_instr_if     ),

    // outputs to ID stage
    .instr_valid_id_o    ( instr_valid_id     ),
    .instr_rdata_id_o    ( instr_rdata_id     ),
    .is_fetch_failed_o   ( is_fetch_failed_id ),

    // control signals
    .clear_instr_valid_i ( clear_instr_valid ),
    .pc_set_i            ( pc_set            ),

    .mepc_i              ( mepc              ), // exception return address

    .dpc_i               ( dpc               ), // debug return address

    .pc_mux_i            ( pc_mux_id         ), // sel for pc multiplexer
    .exc_pc_mux_i        ( exc_pc_mux_id     ),


    .pc_id_o             ( pc_id             ),
    .pc_if_o             ( pc_if             ),

    .is_compressed_id_o  ( is_compressed_id  ),
    .illegal_c_insn_id_o ( illegal_c_insn_id ),

    .m_exc_vec_pc_mux_i  ( m_exc_vec_pc_mux_id ),

    .csr_mtvec_init_o    ( csr_mtvec_init    ),

    // Jump targets
    .jump_target_id_i    ( jump_target_id    ),
    .jump_target_ex_i    ( jump_target_ex    ),

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

    // Processor Enable
    .fetch_enable_i               ( fetch_enable         ),     // Delayed version so that clock can remain gated until fetch enabled
    .ctrl_busy_o                  ( ctrl_busy            ),
    .is_decoding_o                ( is_decoding          ),

    // Interface to instruction memory
    .instr_valid_i                ( instr_valid_id       ),
    .instr_rdata_i                ( instr_rdata_id       ),
    .instr_req_o                  ( instr_req_int        ),

    // Jumps and branches
    .branch_decision_i            ( branch_decision      ),
    .jump_target_o                ( jump_target_id       ),

    // IF and ID control signals
    .clear_instr_valid_o          ( clear_instr_valid    ),
    .pc_set_o                     ( pc_set               ),
    .pc_mux_o                     ( pc_mux_id            ),
    .exc_pc_mux_o                 ( exc_pc_mux_id        ),
    .exc_cause_o                  ( exc_cause            ),

    .pc_id_i                      ( pc_id                ),

    .is_compressed_i              ( is_compressed_id     ),
    .illegal_c_insn_i             ( illegal_c_insn_id    ),

    // Stalls
    .halt_if_o                    ( halt_if              ),

    .id_ready_o                   ( id_ready             ),
    .ex_ready_i                   ( ex_ready             ),
    .wb_ready_i                   ( lsu_ready_wb         ),

    .id_valid_o                   ( id_valid             ),
    .ex_valid_i                   ( ex_valid             ),

    // ID/EX pipeline
    .id_ex_pipe_o                 ( id_ex_pipe           ),

    // CSR ID/EX
    .current_priv_lvl_i           ( current_priv_lvl     ),
    .csr_cause_o                  ( csr_cause            ),
    .csr_save_if_o                ( csr_save_if          ), // control signal to save pc
    .csr_save_id_o                ( csr_save_id          ), // control signal to save pc
    .csr_save_ex_o                ( csr_save_ex          ), // control signal to save pc
    .csr_restore_mret_id_o        ( csr_restore_mret_id  ), // control signal to restore pc

    .csr_restore_dret_id_o        ( csr_restore_dret_id  ), // control signal to restore pc

    .csr_save_cause_o             ( csr_save_cause       ),

   // LSU
    .data_misaligned_i            ( data_misaligned      ),

    // Interrupt Signals
    .irq_i                        ( irq_i                ),
    .mie_bypass_i                 ( mie_bypass           ),
    .mip_o                        ( mip                  ),
    .m_irq_enable_i               ( m_irq_enable         ),
    .irq_ack_o                    ( irq_ack_o            ),
    .irq_id_o                     ( irq_id_o             ),

    // Debug Signal
    .debug_mode_o                 ( debug_mode           ),
    .debug_cause_o                ( debug_cause          ),
    .debug_csr_save_o             ( debug_csr_save       ),
    .debug_req_i                  ( debug_req_i          ),
    .debug_havereset_o            ( debug_havereset_o    ),
    .debug_running_o              ( debug_running_o      ),
    .debug_halted_o               ( debug_halted_o       ),
    .debug_single_step_i          ( debug_single_step    ),
    .debug_ebreakm_i              ( debug_ebreakm        ),
    .trigger_match_i              ( trigger_match        ),

    // Wakeup Signal
    .wake_from_sleep_o            ( wake_from_sleep      ),

    // Forward Signals
    .regfile_waddr_wb_i           ( regfile_waddr_fw_wb_o),  // Write address ex-wb pipeline
    .regfile_we_wb_i              ( regfile_we_wb        ),  // write enable for the register file
    .regfile_wdata_wb_i           ( regfile_wdata        ),  // write data to commit in the register file

    .regfile_alu_waddr_fw_i       ( regfile_alu_waddr_fw ),
    .regfile_alu_we_fw_i          ( regfile_alu_we_fw    ),
    .regfile_alu_wdata_fw_i       ( regfile_alu_wdata_fw ),

    // from ALU
    .mult_multicycle_i            ( mult_multicycle      ),

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

    .perf_imiss_i                 ( perf_imiss           )
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
    // Global signals: Clock and active low asynchronous reset
    .clk                        ( clk                          ),
    .rst_n                      ( rst_ni                       ),

    // ID/EX pipeline
    .id_ex_pipe_i               ( id_ex_pipe                   ),

    .mult_multicycle_o          ( mult_multicycle              ), // to ID/EX pipe registers
   
    .lsu_rdata_i                ( lsu_rdata                    ),

    // interface with CSRs
    .csr_rdata_i                ( csr_rdata                    ),

    // Output of ex stage pipeline
    .regfile_waddr_wb_o         ( regfile_waddr_fw_wb_o        ),
    .regfile_we_wb_o            ( regfile_we_wb                ),
    .regfile_wdata_wb_o         ( regfile_wdata                ),

    // To IF: Jump and branch target and decision
    .jump_target_o              ( jump_target_ex               ),
    .branch_decision_o          ( branch_decision              ),

    // To ID stage: Forwarding signals
    .regfile_alu_waddr_fw_o     ( regfile_alu_waddr_fw         ),
    .regfile_alu_we_fw_o        ( regfile_alu_we_fw            ),
    .regfile_alu_wdata_fw_o     ( regfile_alu_wdata_fw         ),

    // stall control
    .is_decoding_i              ( is_decoding                  ),
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

  cv32e40x_load_store_unit load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_ni             ),

    //output to data memory
    .m_obi_data_if         ( m_obi_data_if      ),
    // ID/EX pipeline
    .id_ex_pipe_i          ( id_ex_pipe         ),
   
    .data_rdata_ex_o       ( lsu_rdata          ),
    .data_misaligned_o     ( data_misaligned    ),

    // control signals
    .lsu_ready_ex_o        ( lsu_ready_ex       ),
    .lsu_ready_wb_o        ( lsu_ready_wb       ),

    .busy_o                ( lsu_busy           )
  );

  // Tracer signal
  assign wb_valid = lsu_ready_wb;


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
    // Interface to CSRs (SRAM like)
    .csr_addr_i                 ( csr_addr               ),
    .csr_wdata_i                ( csr_wdata              ),
    .csr_op_i                   ( csr_op                 ),
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
    .dpc_o                      ( dpc                   ),
    .debug_single_step_o        ( debug_single_step      ),
    .debug_ebreakm_o            ( debug_ebreakm          ),
    .trigger_match_o            ( trigger_match          ),

    .priv_lvl_o                 ( current_priv_lvl       ),

    .pc_if_i                    ( pc_if                  ),
    .pc_id_i                    ( pc_id                  ),
    .pc_ex_i                    ( id_ex_pipe.pc          ),

    .csr_save_if_i              ( csr_save_if            ),
    .csr_save_id_i              ( csr_save_id            ),
    .csr_save_ex_i              ( csr_save_ex            ),
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

  //  CSR access
  assign csr_addr     =  csr_addr_int;
  assign csr_wdata    =  id_ex_pipe.alu_operand_a;
  assign csr_op       =  id_ex_pipe.csr_op;

  assign csr_addr_int = csr_num_e'(id_ex_pipe.csr_access ? id_ex_pipe.alu_operand_b[11:0] : '0);


 

`ifdef CV32E40P_ASSERT_ON

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

  
  generate
  begin : gen_no_pulp_cluster_assertions
    // Check that a taken IRQ is actually enabled (e.g. that we do not react to an IRQ that was just disabled in MIE)
    // The actual mie_n value may be different from mie_q if mie is not
    // written to. Changed to mie_bypass_o as this will always
    // correctly reflect the new/old value of mie
    property p_irq_enabled_0;
       @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |->
         (cs_registers_i.mie_bypass_o[exc_cause] && cs_registers_i.mstatus_q.mie);
    endproperty

    a_irq_enabled_0 : assert property(p_irq_enabled_0);

    // Check that a taken IRQ was for an enabled cause and that mstatus.mie gets disabled
    property p_irq_enabled_1;
       @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |=>
         (cs_registers_i.mcause_q[31] && cs_registers_i.mie_q[cs_registers_i.mcause_q[4:0]] && !cs_registers_i.mstatus_q.mie);
    endproperty

    a_irq_enabled_1 : assert property(p_irq_enabled_1);
  end
  endgenerate

  generate
  begin : gen_no_pulp_xpulp_assertions

    // Illegal, ECALL, EBRK checks excluded for PULP due to other definition for for Hardware Loop

    // First illegal instruction decoded
    logic         first_illegal_found;
    logic         first_ecall_found;
    logic         first_ebrk_found;
    logic [31:0]  expected_illegal_mepc;
    logic [31:0]  expected_ecall_mepc;
    logic [31:0]  expected_ebrk_mepc;

    always_ff @(posedge clk , negedge rst_ni)
    begin
      if (rst_ni == 1'b0) begin
        first_illegal_found   <= 1'b0;
        first_ecall_found     <= 1'b0;
        first_ebrk_found      <= 1'b0;
        expected_illegal_mepc <= 32'b0;
        expected_ecall_mepc   <= 32'b0;
        expected_ebrk_mepc    <= 32'b0;
      end
      else begin
        if (!first_illegal_found && is_decoding && id_valid && id_stage_i.illegal_insn && !id_stage_i.controller_i.debug_mode_n) begin
          first_illegal_found   <= 1'b1;
          expected_illegal_mepc <= pc_id;
        end
        if (!first_ecall_found && is_decoding && id_valid && id_stage_i.ecall_insn && !id_stage_i.controller_i.debug_mode_n) begin
          first_ecall_found   <= 1'b1;
          expected_ecall_mepc <= pc_id;
        end
        if (!first_ebrk_found && is_decoding && id_valid && id_stage_i.ebrk_insn && (id_stage_i.controller_i.ctrl_fsm_ns != DBG_FLUSH)) begin
          first_ebrk_found   <= 1'b1;
          expected_ebrk_mepc <= pc_id;
        end
      end
    end

    // First mepc write for illegal instruction exception
    logic         first_cause_illegal_found;
    logic         first_cause_ecall_found;
    logic         first_cause_ebrk_found;
    logic [31:0]  actual_illegal_mepc;
    logic [31:0]  actual_ecall_mepc;
    logic [31:0]  actual_ebrk_mepc;

    always_ff @(posedge clk , negedge rst_ni)
    begin
      if (rst_ni == 1'b0) begin
        first_cause_illegal_found <= 1'b0;
        first_cause_ecall_found   <= 1'b0;
        first_cause_ebrk_found    <= 1'b0;
        actual_illegal_mepc       <= 32'b0;
        actual_ecall_mepc         <= 32'b0;
        actual_ebrk_mepc          <= 32'b0;
      end
      else begin
        if (!first_cause_illegal_found && (cs_registers_i.csr_cause_i == {1'b0, EXC_CAUSE_ILLEGAL_INSN}) && csr_save_cause) begin
          first_cause_illegal_found <= 1'b1;
          actual_illegal_mepc       <= cs_registers_i.mepc_n;
        end
        if (!first_cause_ecall_found && (cs_registers_i.csr_cause_i == {1'b0, EXC_CAUSE_ECALL_MMODE}) && csr_save_cause) begin
          first_cause_ecall_found <= 1'b1;
          actual_ecall_mepc       <= cs_registers_i.mepc_n;
        end
        if (!first_cause_ebrk_found && (cs_registers_i.csr_cause_i == {1'b0, EXC_CAUSE_BREAKPOINT}) && csr_save_cause) begin
          first_cause_ebrk_found <= 1'b1;
          actual_ebrk_mepc       <= cs_registers_i.mepc_n;
        end
      end
    end

    // Check that mepc is updated with PC of illegal instruction
    property p_illegal_mepc;
       @(posedge clk) disable iff (!rst_ni) (first_illegal_found && first_cause_illegal_found) |=> (expected_illegal_mepc == actual_illegal_mepc);
    endproperty

    a_illegal_mepc : assert property(p_illegal_mepc);

    // Check that mepc is updated with PC of the ECALL instruction
    property p_ecall_mepc;
       @(posedge clk) disable iff (!rst_ni) (first_ecall_found && first_cause_ecall_found) |=> (expected_ecall_mepc == actual_ecall_mepc);
    endproperty

    a_ecall_mepc : assert property(p_ecall_mepc);

    // Check that mepc is updated with PC of EBRK instruction
    property p_ebrk_mepc;
       @(posedge clk) disable iff (!rst_ni) (first_ebrk_found && first_cause_ebrk_found) |=> (expected_ebrk_mepc == actual_ebrk_mepc);
    endproperty

    a_ebrk_mepc : assert property(p_ebrk_mepc);

  end
  endgenerate

  // Single Step only decodes one instruction in non debug mode and next instruction decode is in debug mode
  logic inst_taken;
  assign inst_taken = id_valid && is_decoding;

  a_single_step : assert property
  (
    @(posedge clk) disable iff (!rst_ni)
    (inst_taken && debug_single_step && ~debug_mode)
    ##1 inst_taken [->1]
    |-> (debug_mode && debug_single_step));

`endif

endmodule
