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
  #(parameter RVFI_NRET = 2)
  (
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic [31:0] hart_id_i,

  input  logic        irq_ack_i,
  input  logic        illegal_insn_id_i,
  input  logic        mret_insn_id_i,
  input  logic        ebrk_insn_id_i,
  input  logic        ecall_insn_id_i,

  input  logic        instr_is_compressed_id_i,
  input  logic [15:0] instr_rdata_c_id_i,
  input  logic [31:0] instr_rdata_id_i,

  input  logic        instr_id_valid_i,
  input  logic        instr_id_is_decoding_i,

  input  logic [31:0] rdata_a_id_i,
  input  logic [4:0]  raddr_a_id_i,
  input  logic [31:0] rdata_b_id_i,
  input  logic [4:0]  raddr_b_id_i,

  input  logic        rd_we_wb_i,
  input  logic [4:0]  rd_addr_wb_i,
  input  logic [31:0] rd_wdata_wb_i,

  input  logic [31:0] pc_id_i,
  input  logic [31:0] pc_if_i,
  input  logic [31:0] jump_target_id_i,

  input  logic        pc_set_i,
  input  logic [2:0]  pc_mux_i, 

  input  logic [1:0]  lsu_type_id_i,
  input  logic        lsu_we_id_i,
  input  logic        lsu_req_id_i,

  input  logic        instr_ex_ready_i,
  input  logic        instr_ex_valid_i,

  input  logic [31:0] branch_target_ex_i,

  input  logic [31:0] lsu_addr_ex_i,
  input  logic [31:0] lsu_wdata_ex_i,
  input  logic        lsu_req_ex_i,
  input  logic        lsu_misagligned_ex_i,
  input  logic        lsu_is_misagligned_ex_i,

  input  logic        lsu_rvalid_wb_i,

  input  logic [31:0] exception_target_wb_i,
  input  logic [31:0] mepc_target_wb_i,

  input  logic        is_debug_mode,

  //CSRs
  input Status_t      csr_mstatus_n_i,
  input Status_t      csr_mstatus_q_i,

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
  output logic [RVFI_NRET-1:0]     rvfi_valid,
  output logic [RVFI_NRET*64-1:0]  rvfi_order,
  output logic [RVFI_NRET*32 -1:0] rvfi_insn,
  output logic [RVFI_NRET-1:0]     rvfi_trap,
  output logic [RVFI_NRET-1:0]     rvfi_halt,
  output logic [RVFI_NRET-1:0]     rvfi_intr,
  output logic [RVFI_NRET*2-1:0]   rvfi_mode,
  output logic [RVFI_NRET*2-1:0]   rvfi_ixl,

  output logic [RVFI_NRET*5-1:0]   rvfi_rs1_addr,
  output logic [RVFI_NRET*5-1:0]   rvfi_rs2_addr,
  output logic [RVFI_NRET*32-1:0]  rvfi_rs1_rdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_rs2_rdata,
  output logic [RVFI_NRET*5-1:0]   rvfi_rd_addr,
  output logic [RVFI_NRET*32-1:0]  rvfi_rd_wdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_pc_rdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_pc_wdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_mem_addr,
  output logic [RVFI_NRET*32/8-1:0]rvfi_mem_rmask,
  output logic [RVFI_NRET*32/8-1:0]rvfi_mem_wmask,
  output logic [RVFI_NRET*32-1:0]  rvfi_mem_rdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_mem_wdata,

  output logic [RVFI_NRET*32-1:0]  rvfi_csr_mstatus_rmask,
  output logic [RVFI_NRET*32-1:0]  rvfi_csr_mstatus_wmask,
  output logic [RVFI_NRET*32-1:0]  rvfi_csr_mstatus_rdata,
  output logic [RVFI_NRET*32-1:0]  rvfi_csr_mstatus_wdata
);

  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs2_data_d;

  logic [4:0]  rvfi_rd_addr_d;

  logic [31:0] rvfi_rd_wdata_d;


  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_addr_d;

  // When writeback stage is present RVFI information is emitted when instruction is finished in
  // third stage but some information must be captured whilst the instruction is in the second
  // stage. Without writeback stage RVFI information is all emitted when instruction retires in
  // second stage. RVFI outputs are all straight from flops. So 2 stage pipeline requires a single
  // set of flops (instr_info => RVFI_out), 3 stage pipeline requires two sets (instr_info => wb
  // => RVFI_out)
  localparam int RVFI_STAGES = 3;

  localparam int NRET_MAX    = 2; // Largest NRET currently supported


  logic  [RVFI_STAGES-1:0] data_req_q;
  logic  [RVFI_STAGES-1:0] mret_q;
  logic  [RVFI_STAGES-1:0] syscall_q;

  logic                    data_misagligned_q;
  logic [RVFI_NRET-1:0]    intr_d;
  logic                    instr_id_done;

  logic         ex_stage_ready_q;
  logic         ex_stage_valid_q;

  logic         is_jump_id;
  logic         is_branch_ex;
  logic         is_exception_wb;
  logic         is_mret_wb;

`ifdef CV32E40X_TRACE_EXECUTION
  `include "cv32e40x_rvfi_trace.svh"
`endif

  rvfi_instr_t rvfi_stage [RVFI_STAGES][NRET_MAX];
  rvfi_intr_t  prev_instr;
  rvfi_intr_t  current_instr;
  rvfi_intr_t  instr_q[RVFI_NRET];

  assign is_jump_id      = (pc_mux_i == PC_JUMP);
  assign is_branch_ex    = (pc_mux_i == PC_BRANCH);
  assign is_exception_wb = (pc_mux_i == PC_EXCEPTION);
  assign is_mret_wb      = (pc_mux_i == PC_MRET);

  generate
    // Assign rvfi channels based on NRET
    for (genvar i = 0; i < RVFI_NRET; i++) begin
      assign rvfi_valid            [i]          = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_valid;
      assign rvfi_order            [(i*64)+:64] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_order;
      assign rvfi_insn             [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_insn;
      assign rvfi_trap             [i]          = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_trap;
      assign rvfi_halt             [i]          = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_halt;
      assign rvfi_intr             [i]          = intr_d[i];
      assign rvfi_mode             [(i* 2)+: 2] = 2'b11; // Privilege level: Machine-mode (3)
      assign rvfi_ixl              [(i* 2)+: 2] = 2'b01; // XLEN for current privilege level, must be 1(32) for RV32 systems
      assign rvfi_rs1_addr         [(i* 5)+: 5] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rs1_addr;
      assign rvfi_rs2_addr         [(i* 5)+: 5] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rs2_addr;
      assign rvfi_rs1_rdata        [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rs1_rdata;
      assign rvfi_rs2_rdata        [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rs2_rdata;
      assign rvfi_rd_addr          [(i* 5)+: 5] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rd_addr;
      assign rvfi_rd_wdata         [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_rd_wdata;
      assign rvfi_pc_rdata         [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_pc_rdata;
      assign rvfi_pc_wdata         [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_pc_wdata;
      assign rvfi_mem_addr         [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_mem_addr;
      assign rvfi_mem_rmask        [(i* 4)+: 4] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_mem_rmask;
      assign rvfi_mem_wmask        [(i* 4)+: 4] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_mem_wmask;
      assign rvfi_mem_rdata        [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_mem_rdata;
      assign rvfi_mem_wdata        [(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_mem_wdata;
      assign rvfi_csr_mstatus_rmask[(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_csr_mstatus_rmask;
      assign rvfi_csr_mstatus_wmask[(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_csr_mstatus_wmask;
      assign rvfi_csr_mstatus_rdata[(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_csr_mstatus_rdata;
      assign rvfi_csr_mstatus_wdata[(i*32)+:32] = rvfi_stage[RVFI_STAGES-RVFI_NRET+i][NRET_MAX-RVFI_NRET+i].rvfi_csr_mstatus_wdata;
    end // for (genvar i = 0; i < RVFI_NRET; i++)

    // An instruction in the ID stage is valid (instr_id_valid_i)
    // when it's not stalled by the EX stage
    // due to stalls in the EX stage, data hazards, or if it is not halted by the controller
    // as due interrupts, debug requests, illegal instructions, ebreaks and ecalls
    assign instr_id_done  = instr_id_valid_i && instr_id_is_decoding_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        ex_stage_ready_q   <= '0;
        ex_stage_valid_q   <= '0;
        data_misagligned_q <= '0;
      end else begin

        // Keep instr in EX valid if next instruction is not valid
        ex_stage_ready_q       <= instr_id_done || !instr_ex_ready_i && ex_stage_ready_q;
        ex_stage_valid_q       <= instr_id_done || !instr_ex_valid_i && ex_stage_valid_q;

        // Handle misaligned state
        if (instr_ex_ready_i && data_req_q[0] && !lsu_misagligned_ex_i) begin
          data_misagligned_q <= lsu_is_misagligned_ex_i;
        end else if (lsu_rvalid_wb_i && data_misagligned_q) begin
          data_misagligned_q <= 1'b0;
        end

      end // else: !if(!rst_ni)
    end // always_ff @

    for (genvar i = 0; i < RVFI_NRET; i++) begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          instr_q[i]      <= '0;
        end else begin
          // Store last valid instructions
          if(rvfi_valid[i]) begin
            instr_q[i].valid    <= rvfi_valid[i];
            instr_q[i].order    <= rvfi_order[(i*64)+:64];
            instr_q[i].pc_wdata <= rvfi_pc_wdata[(i*32)+:32];
          end
        end
      end // always_ff @
    end // for (genvar i = 0; i < RVFI_NRET; i++)

    always_comb begin
      // Find previous instruction
      prev_instr = '0;

      // Look for latest instruction in retired instructions
      // The the rvfi channel with the lowest index will have the highest order number
      for (int i = RVFI_NRET-1;  i >= 0; i--) begin
        if (instr_q[i].valid) begin
          prev_instr = instr_q[i];
        end
      end

      // Check if there is a second latest valid instruction in current rvfi channels
      current_instr = prev_instr;
      for (int i = RVFI_NRET-1;  i >= 0; i--) begin
        if (rvfi_valid[i]) begin
          prev_instr          = current_instr;
          current_instr.valid = 1'b1;
          current_instr.order = rvfi_order[i*64+:64];
          current_instr.valid = rvfi_pc_rdata[i*32+:32];
        end
      end
    end

    // Check if instruction is the first instruction in trap handler
    for (genvar i = 0; i < RVFI_NRET; i++) begin
      assign intr_d[i] = prev_instr.valid                                 && // Previous instruction valid
                         rvfi_valid[i]                                    && // Current instruction valid
                         ((rvfi_order[i*64+:64] - prev_instr.order) == 1) && // Is latest instruction
                         (rvfi_pc_rdata[i*32+:32]  != prev_instr.pc_wdata);  // Is first part of trap handler
    end

  endgenerate

  // Pipeline stage model //

  for (genvar i = 0;i < RVFI_STAGES; i = i + 1) begin : g_rvfi_stages
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin

        rvfi_stage[i][0]            <= rvfi_instr_t'(0);
        rvfi_stage[i][1]            <= rvfi_instr_t'(0);

        rvfi_stage[i][0].rvfi_csr_mstatus_rmask <= 32'hFFFF_FFFF;
        rvfi_stage[i][0].rvfi_csr_mstatus_wmask <= 32'hFFFF_FFFF;

        data_req_q[i]               <= '0;
        mret_q[i]                   <= '0;
        syscall_q[i]                <= '0;

      end else begin

        // Signals valid in ID stage
        // all the instructions treated the same
        if (i == 0) begin

          rvfi_stage[i][0].rvfi_valid    <= instr_id_done;

          if(instr_id_done) begin

            rvfi_stage[i][0].rvfi_halt      <= 1'b0;
            rvfi_stage[i][0].rvfi_trap      <= illegal_insn_id_i;
            rvfi_stage[i][0].rvfi_intr      <= 1'b0;
            rvfi_stage[i][0].rvfi_order     <= rvfi_stage[i][0].rvfi_order + 64'b1;
            rvfi_stage[i][0].rvfi_insn      <= rvfi_insn_id;

            rvfi_stage[i][0].rvfi_rs1_addr  <= rvfi_rs1_addr_d;
            rvfi_stage[i][0].rvfi_rs2_addr  <= rvfi_rs2_addr_d;
            rvfi_stage[i][0].rvfi_rs1_rdata <= rvfi_rs1_data_d;
            rvfi_stage[i][0].rvfi_rs2_rdata <= rvfi_rs2_data_d;

            rvfi_stage[i][0].rvfi_pc_rdata  <= pc_id_i;
            rvfi_stage[i][0].rvfi_pc_wdata  <= (pc_set_i && is_jump_id) ? jump_target_id_i : pc_if_i;

            rvfi_stage[i][0].rvfi_mem_rmask <= (lsu_req_id_i && !lsu_we_id_i) ? rvfi_mem_mask_int : 4'b0000;
            rvfi_stage[i][0].rvfi_mem_wmask <= (lsu_req_id_i &&  lsu_we_id_i) ? rvfi_mem_mask_int : 4'b0000;

            data_req_q[i]                   <= lsu_req_id_i;
            mret_q[i]                       <= mret_insn_id_i;
            syscall_q[i]                    <= ebrk_insn_id_i || ecall_insn_id_i;

          end
        end else if (i == 1) begin
          // No instructions retiring in the EX stage

          if(instr_ex_ready_i && !data_req_q[i-1] && !(rvfi_stage[i-1][0].rvfi_trap || mret_q[i-1] || syscall_q[i-1])) begin

            rvfi_stage[i][1]                <= rvfi_stage[i-1][0];

            rvfi_stage[i][1].rvfi_valid     <= ex_stage_ready_q;

            rvfi_stage[i][1].rvfi_pc_wdata <= pc_set_i && is_branch_ex ? branch_target_ex_i : rvfi_stage[i-1][0].rvfi_pc_wdata;

            //csr operations as READ, WRITE, SET, CLEAR (does not work yet with interrupts)
            rvfi_stage[i][1].rvfi_csr_mstatus_wdata <= {14'b0,csr_mstatus_n_i.mprv,4'b0,csr_mstatus_n_i.mpp,3'b0,csr_mstatus_n_i.mpie,2'h0,csr_mstatus_n_i.upie,csr_mstatus_n_i.mie,2'h0,csr_mstatus_n_i.uie};
            rvfi_stage[i][1].rvfi_csr_mstatus_rdata <= {14'b0,csr_mstatus_q_i.mprv,4'b0,csr_mstatus_q_i.mpp,3'b0,csr_mstatus_q_i.mpie,2'h0,csr_mstatus_q_i.upie,csr_mstatus_q_i.mie,2'h0,csr_mstatus_q_i.uie};

            //clean up data_req_q[1] when the previous ld/st retired
            if(data_req_q[i]) begin
              if(lsu_rvalid_wb_i && rvfi_stage[i][1].rvfi_valid && !data_misagligned_q)
                data_req_q[i] <= 1'b0;
            end
            mret_q[i]                  <= mret_q[i-1];
            syscall_q[i]               <= syscall_q[i-1];

          end else begin
            rvfi_stage[i][1].rvfi_valid <= 1'b0;
          end


          //memory operations
          if(instr_ex_ready_i && data_req_q[i-1]) begin
            //true during first data req if GNT
            if(!lsu_misagligned_ex_i) begin

              rvfi_stage[i][1]                <= rvfi_stage[i-1][0];
              rvfi_stage[i][1].rvfi_valid     <= ex_stage_ready_q;

              rvfi_stage[i][1].rvfi_mem_addr  <= rvfi_mem_addr_d;
              rvfi_stage[i][1].rvfi_mem_wdata <= rvfi_mem_wdata_d;
              data_req_q[i]                   <= data_req_q[i-1];
              mret_q[i]                       <= mret_q[i-1];
              syscall_q[i]                    <= syscall_q[i-1];
            end
          end

          //exceptions
          if(instr_ex_valid_i && (rvfi_stage[i-1][0].rvfi_trap || mret_q[i-1] || syscall_q[i-1])) begin

              rvfi_stage[i][1]                <= rvfi_stage[i-1][1];
              rvfi_stage[i][1].rvfi_valid     <= ex_stage_valid_q;

              rvfi_stage[i][1].rvfi_mem_addr  <= rvfi_mem_addr_d;
              rvfi_stage[i][1].rvfi_mem_wdata <= rvfi_mem_wdata_d;

              //exceptions as illegal, and syscalls
              rvfi_stage[i][1].rvfi_csr_mstatus_wdata <= {14'b0,csr_mstatus_n_i.mprv,4'b0,csr_mstatus_n_i.mpp,3'b0,csr_mstatus_n_i.mpie,2'h0,csr_mstatus_n_i.upie,csr_mstatus_n_i.mie,2'h0,csr_mstatus_n_i.uie};
              rvfi_stage[i][1].rvfi_csr_mstatus_rdata <= {14'b0,csr_mstatus_q_i.mprv,4'b0,csr_mstatus_q_i.mpp,3'b0,csr_mstatus_q_i.mpie,2'h0,csr_mstatus_q_i.upie,csr_mstatus_q_i.mie,2'h0,csr_mstatus_q_i.uie};

              data_req_q[i]                   <= 1'b0;
              mret_q[i]                       <= mret_q[i-1];
              syscall_q[i]                    <= syscall_q[i-1];
          end // if (instr_ex_valid_i && (rvfi_stage[i-1][0].rvfi_trap || mret_q[i-1] || syscall_q[i-1]))

        end else if (i == 2) begin
        // Signals valid in WB stage

          case(1'b1)

            //memory operations
            lsu_rvalid_wb_i && data_req_q[i-1]: begin
              rvfi_stage[i][1]                <= rvfi_stage[i-1][1];
              //misaligneds take 2 cycles at least
              rvfi_stage[i][1].rvfi_valid     <= rvfi_stage[i-1][1].rvfi_valid && !data_misagligned_q;
              //rvfi_stage[i][1].rvfi_mem_rdata <= rvfi_rd2_wdata_d;
              rvfi_stage[i][1].rvfi_mem_rdata <= 'x; //fixme
            end
            //traps
            rvfi_stage[i-1][1].rvfi_trap: begin
              rvfi_stage[i][1]                <= rvfi_stage[i-1][1];
            end
            //ebreaks, ecall, fence.i
            syscall_q[i-1]: begin
              rvfi_stage[i][1]                <= rvfi_stage[i-1][1];
              rvfi_stage[i][1].rvfi_pc_wdata  <= exception_target_wb_i;
            end
            //mret
            (mret_q[i-1] && rvfi_stage[i-1][1].rvfi_valid ) || mret_q[i]: begin
              //the MRET retires in one extra cycle, thus
              rvfi_stage[i][1]                <= rvfi_stage[i-1][1];
              rvfi_stage[i][1].rvfi_valid     <= mret_q[i];
              rvfi_stage[i][1].rvfi_pc_wdata  <= is_mret_wb ? mepc_target_wb_i : exception_target_wb_i;
              if(!mret_q[i]) begin
                //first cyle of MRET (FLUSH_WB)
                rvfi_stage[i][1].rvfi_csr_mstatus_wdata <= {14'b0,csr_mstatus_n_i.mprv,4'b0,csr_mstatus_n_i.mpp,3'b0,csr_mstatus_n_i.mpie,2'h0,csr_mstatus_n_i.upie,csr_mstatus_n_i.mie,2'h0,csr_mstatus_n_i.uie};
                rvfi_stage[i][1].rvfi_csr_mstatus_rdata <= {14'b0,csr_mstatus_q_i.mprv,4'b0,csr_mstatus_q_i.mpp,3'b0,csr_mstatus_q_i.mpie,2'h0,csr_mstatus_q_i.upie,csr_mstatus_q_i.mie,2'h0,csr_mstatus_q_i.uie};
              end

              mret_q[i]                       <= !mret_q[i];
            end
            rvfi_stage[i-1][1].rvfi_valid: begin
              rvfi_stage[i][1]               <= rvfi_stage[i-1][1];
              rvfi_stage[i][1].rvfi_rd_addr  <= (rd_we_wb_i) ? rvfi_rd_addr_d  : '0;
              rvfi_stage[i][1].rvfi_rd_wdata <= (rd_we_wb_i) ? rvfi_rd_wdata_d : '0;
            end

            default:
              rvfi_stage[i][1].rvfi_valid     <= 1'b0;
            endcase
        end
      end
    end
  end

  // Byte enable based on data type
  always_comb begin
    unique case (lsu_type_id_i)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  // Memory adddress
  assign rvfi_mem_addr_d = lsu_addr_ex_i;

  // Memory write data
  assign rvfi_mem_wdata_d = lsu_wdata_ex_i;


  always_comb begin
    if (instr_is_compressed_id_i) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id_i};
    end else begin
      rvfi_insn_id = instr_rdata_id_i;
    end
  end

  // Source registers
  assign rvfi_rs1_addr_d = raddr_a_id_i;
  assign rvfi_rs2_addr_d = raddr_b_id_i;

  assign rvfi_rs1_data_d = (raddr_a_id_i == '0)   ? '0 : rdata_a_id_i;
  assign rvfi_rs2_data_d = (raddr_b_id_i == '0)   ? '0 : rdata_b_id_i;

  // Destination register
  assign rvfi_rd_addr_d  = (!rd_we_wb_i)          ? '0 : rd_addr_wb_i;
  assign rvfi_rd_wdata_d = (rvfi_rd_addr_d == '0) ? '0 : rd_wdata_wb_i;

endmodule // cv32e40x_rvfi

