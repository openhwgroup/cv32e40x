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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_if_stage import cv32e40x_pkg::*;
#(
  parameter bit          A_EXT           = 0,
  parameter bit          X_EXT           = 0,
  parameter int          X_ID_WIDTH      = 4,
  parameter int          PMA_NUM_REGIONS = 0,
  parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT}
)
(
  input  logic          clk,
  input  logic          rst_n,

  // Target addresses
  input  logic [31:0]   boot_addr_i,            // Boot address
  input  logic [31:0]   branch_target_ex_i,     // Branch target address
  input  logic [31:0]   dm_exception_addr_i,    // Debug mode exception address
  input  logic [31:0]   dm_halt_addr_i,         // Debug mode halt address
  input  logic [31:0]   dpc_i,                  // Debug PC (restore upon return from debug)
  input  logic [31:0]   jump_target_id_i,       // Jump target address
  input  logic [31:0]   mepc_i,                 // Exception PC (restore upon return from exception/interrupt)
  input  logic [23:0]   mtvec_addr_i,           // Exception/interrupt address (MSBs)
  input  logic [31:0]   nmi_addr_i,             // NMI address

  input ctrl_fsm_t      ctrl_fsm_i,
  input  logic          trigger_match_i,

  // Instruction bus interface
  if_c_obi.master       m_c_obi_instr_if,

  output if_id_pipe_t   if_id_pipe_o,           // IF/ID pipeline stage
  output logic [31:0]   pc_if_o,                // Program counter
  output logic          csr_mtvec_init_o,       // Tell CS regfile to init mtvec
  output logic          if_busy_o,              // Is the IF stage busy fetching instructions?

  // Stage ready/valid
  output logic          if_valid_o,
  input  logic          id_ready_i,

  // eXtension interface
  if_xif.cpu_compressed xif_compressed_if,      // XIF compressed interface
  input  logic          xif_offloading_id_i     // ID stage attempts to offload an instruction
);

  logic              if_ready;

  // prefetch buffer related signals
  logic              prefetch_busy;

  logic       [31:0] branch_addr_n;

  logic              prefetch_valid;
  inst_resp_t        prefetch_instr;

  logic              illegal_c_insn;

  inst_resp_t        instr_decompressed;
  logic              instr_compressed_int;

  // Transaction signals to/from obi interface
  logic              prefetch_resp_valid;
  logic              prefetch_trans_valid;
  logic              prefetch_trans_ready;
  logic [31:0]       prefetch_trans_addr;
  inst_resp_t        prefetch_inst_resp;
  logic              prefetch_one_txn_pend_n;

  logic              bus_resp_valid;
  obi_inst_resp_t    bus_resp;
  logic              bus_trans_valid;
  logic              bus_trans_ready;
  obi_inst_req_t     bus_trans;
  obi_inst_req_t     core_trans;

  // Local instr_valid
  logic instr_valid;

  // eXtension interface signals
  logic [X_ID_WIDTH-1:0] xif_id;

  // Fetch address selection
  always_comb
  begin
    // Default assign PC_BOOT (should be overwritten in below case)
    branch_addr_n = {boot_addr_i[31:2], 2'b0};

    unique case (ctrl_fsm_i.pc_mux)
      PC_BOOT:     branch_addr_n = {boot_addr_i[31:2], 2'b0};
      PC_JUMP:     branch_addr_n = jump_target_id_i;
      PC_BRANCH:   branch_addr_n = branch_target_ex_i;
      PC_MRET:     branch_addr_n = mepc_i;                                                      // PC is restored when returning from IRQ/exception
      PC_DRET:     branch_addr_n = dpc_i;
      PC_FENCEI:   branch_addr_n = ctrl_fsm_i.pipe_pc;                                          // Jump to next instruction forces prefetch buffer reload
      PC_TRAP_EXC: branch_addr_n = {mtvec_addr_i, 8'h0 };                                       // All the exceptions go to base address
      PC_TRAP_IRQ: branch_addr_n = {mtvec_addr_i, 1'b0, ctrl_fsm_i.m_exc_vec_pc_mux, 2'b0};     // interrupts are vectored
      PC_TRAP_DBD: branch_addr_n = {dm_halt_addr_i[31:2], 2'b0};
      PC_TRAP_DBE: branch_addr_n = {dm_exception_addr_i[31:2], 2'b0};
      PC_TRAP_NMI: branch_addr_n = {nmi_addr_i[31:2], 2'b00};
      default:;
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (ctrl_fsm_i.pc_mux == PC_BOOT) & ctrl_fsm_i.pc_set;

  // prefetch buffer, caches a fixed number of instructions
  cv32e40x_prefetch_unit prefetch_unit_i
  (
    .clk               ( clk                         ),
    .rst_n             ( rst_n                       ),

    .ctrl_fsm_i        ( ctrl_fsm_i                  ),

    .branch_addr_i     ( {branch_addr_n[31:1], 1'b0} ),

    .prefetch_ready_i  ( if_ready                    ),
    .prefetch_valid_o  ( prefetch_valid              ),
    .prefetch_instr_o  ( prefetch_instr              ),
    .prefetch_addr_o   ( pc_if_o                     ),

    .trans_valid_o     ( prefetch_trans_valid        ),
    .trans_ready_i     ( prefetch_trans_ready        ),
    .trans_addr_o      ( prefetch_trans_addr         ),

    .resp_valid_i      ( prefetch_resp_valid         ),
    .resp_i            ( prefetch_inst_resp          ),

    // Prefetch Buffer Status
    .prefetch_busy_o   ( prefetch_busy               ),
    .one_txn_pend_n    ( prefetch_one_txn_pend_n     )
  );

  //////////////////////////////////////////////////////////////////////////////
  // MPU
  //////////////////////////////////////////////////////////////////////////////

  assign core_trans.addr = prefetch_trans_addr;
  assign core_trans.dbg  = ctrl_fsm_i.debug_mode_if;
  assign core_trans.prot[0] = 1'b0;                     // Transfers from IF stage are instruction transfers
  assign core_trans.prot[2:1] = PRIV_LVL_M;             // Machine mode
  assign core_trans.memtype = 2'b00;                    // memtype is assigned in the MPU, tie off.

  cv32e40x_mpu
  #(
    .IF_STAGE             ( 1                       ),
    .A_EXT                ( A_EXT                   ),
    .CORE_REQ_TYPE        ( obi_inst_req_t          ),
    .CORE_RESP_TYPE       ( inst_resp_t             ),
    .BUS_RESP_TYPE        ( obi_inst_resp_t         ),
    .PMA_NUM_REGIONS      ( PMA_NUM_REGIONS         ),
    .PMA_CFG              ( PMA_CFG                 )
  )
  mpu_i
  (
    .clk                  ( clk                     ),
    .rst_n                ( rst_n                   ),
    .atomic_access_i      ( 1'b0                    ), // No atomic transfers on instruction side
    .misaligned_access_i  ( 1'b0                    ), // MPU on instruction side will not issue misaligned access fault
                                                       // Misaligned access to main is allowed, and accesses outside main will
                                                       // result in instruction access fault (which will have priority over
                                                       //  misaligned from I/O fault)
    .core_one_txn_pend_n  ( prefetch_one_txn_pend_n ),
    .core_trans_valid_i   ( prefetch_trans_valid    ),
    .core_trans_ready_o   ( prefetch_trans_ready    ),
    .core_trans_i         ( core_trans              ),
    .core_resp_valid_o    ( prefetch_resp_valid     ),
    .core_resp_o          ( prefetch_inst_resp      ),

    .bus_trans_valid_o    ( bus_trans_valid         ),
    .bus_trans_ready_i    ( bus_trans_ready         ),
    .bus_trans_o          ( bus_trans               ),
    .bus_resp_valid_i     ( bus_resp_valid          ),
    .bus_resp_i           ( bus_resp                )
  );

  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_instr_obi_interface
  instruction_obi_i
  (
    .clk                  ( clk              ),
    .rst_n                ( rst_n            ),

    .trans_valid_i        ( bus_trans_valid  ),
    .trans_ready_o        ( bus_trans_ready  ),
    .trans_i              ( bus_trans        ),

    .resp_valid_o         ( bus_resp_valid   ),
    .resp_o               ( bus_resp         ),
    .m_c_obi_instr_if     ( m_c_obi_instr_if )
  );

  // Local instr_valid when we have valid output from prefetcher
  // and IF is not halted or killed
  assign instr_valid = prefetch_valid && !ctrl_fsm_i.kill_if && !ctrl_fsm_i.halt_if;

  // if_stage ready when killed, otherwise when not halted.
  assign if_ready = ctrl_fsm_i.kill_if || (id_ready_i && !ctrl_fsm_i.halt_if);

  // if stage valid when local instr_valid is 1
  assign if_valid_o = instr_valid;

  assign if_busy_o = prefetch_busy;

  // Populate instruction meta data
  instr_meta_t instr_meta_n; 
  always_comb begin
    instr_meta_n = '0;
    instr_meta_n.compressed = instr_compressed_int;
  end

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0) begin
      if_id_pipe_o.instr_valid      <= 1'b0;
      if_id_pipe_o.instr            <= INST_RESP_RESET_VAL;
      if_id_pipe_o.instr_meta       <= '0;
      if_id_pipe_o.pc               <= '0;
      if_id_pipe_o.illegal_c_insn   <= 1'b0;
      if_id_pipe_o.compressed_instr <= '0;
      if_id_pipe_o.trigger_match    <= 1'b0;
      if_id_pipe_o.xif_id           <= '0;
    end else begin
      // Valid pipeline output if we are valid AND the
      // alignment buffer has a valid instruction
      if (if_valid_o && id_ready_i) begin
        if_id_pipe_o.instr_valid      <= 1'b1;
        if_id_pipe_o.instr            <= instr_decompressed;
        if_id_pipe_o.instr_meta       <= instr_meta_n;
        if_id_pipe_o.illegal_c_insn   <= illegal_c_insn;
        if_id_pipe_o.pc               <= pc_if_o;
        if_id_pipe_o.compressed_instr <= prefetch_instr.bus_resp.rdata[15:0];
        if_id_pipe_o.trigger_match    <= trigger_match_i;
        if_id_pipe_o.xif_id           <= xif_id;
      end else if (id_ready_i) begin
        if_id_pipe_o.instr_valid      <= 1'b0;
      end
    end
  end

  cv32e40x_compressed_decoder
  compressed_decoder_i
  (
    .instr_i         ( prefetch_instr          ),
    .instr_o         ( instr_decompressed      ),
    .is_compressed_o ( instr_compressed_int    ),
    .illegal_instr_o ( illegal_c_insn          )
  );


  //---------------------------------------------------------------------------
  // eXtension interface
  //---------------------------------------------------------------------------

  generate
    if (X_EXT) begin : x_ext

      // TODO: implement offloading of compressed instruction
      assign xif_compressed_if.compressed_valid = '0;
      assign xif_compressed_if.compressed_req   = '0;

      // TODO: assert that the oustanding IDs are unique
      assign xif_id = xif_offloading_id_i ? if_id_pipe_o.xif_id + 1 : if_id_pipe_o.xif_id;

    end else begin : no_x_ext

      assign xif_compressed_if.compressed_valid = '0;
      assign xif_compressed_if.compressed_req   = '0;

      assign xif_id                             = '0;

    end
  endgenerate

endmodule // cv32e40x_if_stage
