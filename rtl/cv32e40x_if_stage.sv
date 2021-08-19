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
  #(parameter bit          A_EXTENSION     = 0,
    parameter int          PMA_NUM_REGIONS = 0,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT})
(
    input  logic        clk,
    input  logic        rst_n,

    // Used to calculate the exception offsets
    input  logic [23:0] mtvec_addr,

    // Boot address
    input  logic [31:0] boot_addr_i,
    input  logic [31:0] dm_exception_addr_i,

    // Debug mode halt address
    input  logic [31:0] dm_halt_addr_i,

    // instruction cache interface
    if_c_obi.master     m_c_obi_instr_if,

    // Output of IF Pipeline stage
    output if_id_pipe_t       if_id_pipe_o,

    // EX_WB pipe
    input  ex_wb_pipe_t       ex_wb_pipe_i,

    input ctrl_fsm_t    ctrl_fsm_i,

    output logic       [31:0] pc_if_o,

    // Forwarding ports - control signals
    input  logic [31:0] mepc_i,                 // address used to restore PC when the interrupt/exception is served

    input  logic [31:0] dpc_i,                  // address used to restore PC when the debug is served

    output logic        csr_mtvec_init_o,       // tell CS regfile to init mtvec

    // jump and branch target and decision
    input  logic [31:0] jump_target_id_i,       // jump target address
    input  logic [31:0] branch_target_ex_i,     // jump target address

    // misc signals
    output logic        if_busy_o,             // Is the IF stage busy fetching instructions?

    // Pipeline handshakes
    output logic        if_valid_o,
    output logic        if_ready_o,
    input  logic        id_ready_i
);

  logic              if_valid, if_ready;

  // prefetch buffer related signals
  logic              prefetch_busy;
  
  logic       [31:0] branch_addr_n;

  logic       [31:0] exc_pc;

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


  // exception PC selection mux
  always_comb
  begin : EXC_PC_MUX
    unique case (ctrl_fsm_i.exc_pc_mux)
      EXC_PC_EXCEPTION:                        exc_pc = { mtvec_addr, 8'h0 }; //1.10 all the exceptions go to base address
      EXC_PC_IRQ:                              exc_pc = { mtvec_addr, 1'b0, ctrl_fsm_i.m_exc_vec_pc_mux, 2'b0 }; // interrupts are vectored
      EXC_PC_DBD:                              exc_pc = { dm_halt_addr_i[31:2], 2'b0 };
      EXC_PC_DBE:                              exc_pc = { dm_exception_addr_i[31:2], 2'b0 };
      default:                                 exc_pc = { mtvec_addr, 8'h0 };
    endcase
  end

  // fetch address selection
  always_comb
  begin
    // Default assign PC_BOOT (should be overwritten in below case)
    branch_addr_n = {boot_addr_i[31:2], 2'b0};

    unique case (ctrl_fsm_i.pc_mux)
      PC_BOOT:      branch_addr_n = {boot_addr_i[31:2], 2'b0};
      PC_JUMP:      branch_addr_n = jump_target_id_i;
      PC_BRANCH:    branch_addr_n = branch_target_ex_i;
      PC_EXCEPTION: branch_addr_n = exc_pc;             // set PC to exception handler
      PC_MRET:      branch_addr_n = mepc_i; // PC is restored when returning from IRQ/exception
      PC_DRET:      branch_addr_n = dpc_i; //
      PC_FENCEI:    branch_addr_n = ex_wb_pipe_i.pc + 4; // jump to next instr forces prefetch buffer reload // TODO:OK:low Can avoid adder, PC should already be in pipeline
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
  assign core_trans.prot[0]   = 1'b0;  // Transfers from IF stage are instruction transfers
  assign core_trans.prot[2:1] = PRIV_LVL_M; // Machine mode
  assign core_trans.memtype   = 2'b00; // memtype is assigned in the MPU, tie off.
  
  cv32e40x_mpu
    #(.IF_STAGE(1),
      .A_EXTENSION(A_EXTENSION),
      .CORE_REQ_TYPE(obi_inst_req_t),
      .CORE_RESP_TYPE(inst_resp_t),
      .BUS_RESP_TYPE(obi_inst_resp_t),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  mpu_i
    (
     .clk                  ( clk   ),
     .rst_n                ( rst_n ),
     .atomic_access_i      ( 1'b0  ), // No atomic transfers on instruction side

     .core_one_txn_pend_n  ( prefetch_one_txn_pend_n ),
     .core_trans_valid_i   ( prefetch_trans_valid    ),
     .core_trans_ready_o   ( prefetch_trans_ready    ),
     .core_trans_i         ( core_trans              ),
     .core_resp_valid_o    ( prefetch_resp_valid     ),
     .core_resp_o          ( prefetch_inst_resp      ),
     
     .bus_trans_valid_o    ( bus_trans_valid ),
     .bus_trans_ready_i    ( bus_trans_ready ),
     .bus_trans_o          ( bus_trans       ),
     .bus_resp_valid_i     ( bus_resp_valid  ),
     .bus_resp_i           ( bus_resp        ));

//////////////////////////////////////////////////////////////////////////////
// OBI interface
//////////////////////////////////////////////////////////////////////////////

cv32e40x_instr_obi_interface
instruction_obi_i
(
  .clk                   ( clk               ),
  .rst_n                 ( rst_n             ),

  .trans_valid_i         ( bus_trans_valid   ),
  .trans_ready_o         ( bus_trans_ready   ),
  .trans_i               ( bus_trans         ),

  .resp_valid_o          ( bus_resp_valid    ),
  .resp_o                ( bus_resp          ),
  .m_c_obi_instr_if      ( m_c_obi_instr_if  )
);

  // if_stage ready if id_stage is ready
  assign if_ready = id_ready_i && !ctrl_fsm_i.halt_if;

  // if stage valid when prefetcher is valid and we are ready
  assign if_valid = if_ready && prefetch_valid;

  assign if_busy_o = prefetch_busy;

  assign if_valid_o = if_valid;
  assign if_ready_o = if_ready;

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      if_id_pipe_o.instr_valid      <= 1'b0;
      if_id_pipe_o.instr            <= INST_RESP_RESET_VAL;
      if_id_pipe_o.pc               <= '0;
      if_id_pipe_o.is_compressed    <= 1'b0;
      if_id_pipe_o.illegal_c_insn   <= 1'b0;
      if_id_pipe_o.compressed_instr <= '0;
    end
    else
    begin
      // Valid pipeline output if we are valid AND the
      // alignment buffer has a valid instruction
      if (if_valid) 
      begin
        if_id_pipe_o.instr_valid      <= 1'b1;
        if_id_pipe_o.instr            <= instr_decompressed;
        if_id_pipe_o.is_compressed    <= instr_compressed_int;
        if_id_pipe_o.illegal_c_insn   <= illegal_c_insn;
        if_id_pipe_o.pc               <= pc_if_o;
        if_id_pipe_o.compressed_instr <= prefetch_instr.bus_resp.rdata[15:0];
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

endmodule // cv32e40x_if_stage
