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
//                                                                            //
// Authors:        Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the core module                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_core_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  (
  input logic        clk,
  input logic        rst_ni,

  input ctrl_fsm_t   ctrl_fsm,
  input logic        id_valid,
  //input logic        multi_cycle_id_stall,
  input logic [4:0]  exc_cause,
  input logic [31:0] mie,
  input logic        debug_single_step,
  input              if_id_pipe_t if_id_pipe,
  input              id_stage_is_last,
   // probed id_stage signals
  /*
  input logic        id_stage_ebrk_insn,
  input logic        id_stage_ecall_insn,
  input logic        id_stage_illegal_insn,
  input logic        id_stage_instr_err,
  input logic        id_stage_mpu_err,
  input logic        id_stage_instr_valid,
  */
  input ex_wb_pipe_t ex_wb_pipe_i,
  input logic        branch_taken_in_ex,
  
   // probed controller signals
  input logic        id_stage_controller_debug_mode_n,
  input              ctrl_state_e ctrl_fsm_ns,
   // probed cs_registers signals
  input logic [31:0] cs_registers_mie_q,
  input logic [31:0] cs_registers_mepc_n,
  input logic [5:0]  cs_registers_csr_cause_i,
  input              Mcause_t cs_registers_mcause_q,
  input              Status_t cs_registers_mstatus_q);



  // Check that a taken IRQ is actually enabled (e.g. that we do not react to an IRQ that was just disabled in MIE)
  // The actual mie_n value may be different from mie_q if mie is not
  // written to.
  property p_irq_enabled_0;
    @(posedge clk) disable iff (!rst_ni)
    (ctrl_fsm.pc_set && (ctrl_fsm.pc_mux == PC_EXCEPTION) && (ctrl_fsm.exc_pc_mux == EXC_PC_IRQ)) |->
    (mie[exc_cause] && cs_registers_mstatus_q.mie);
  endproperty

  a_irq_enabled_0 : assert property(p_irq_enabled_0) else `uvm_error("core", "Assertion a_irq_enabled_0 failed")

  // Check that a taken IRQ was for an enabled cause and that mstatus.mie gets disabled
  property p_irq_enabled_1;
    @(posedge clk) disable iff (!rst_ni)
      (ctrl_fsm.pc_set && (ctrl_fsm.pc_mux == PC_EXCEPTION) && (ctrl_fsm.exc_pc_mux == EXC_PC_IRQ)) |=>
      (cs_registers_mcause_q[31] && cs_registers_mie_q[cs_registers_mcause_q[4:0]] && !cs_registers_mstatus_q.mie);
  endproperty

  a_irq_enabled_1 : assert property(p_irq_enabled_1) else `uvm_error("core", "Assertion a_irq_enabled_1 failed")


// First illegal instruction decoded
logic         first_illegal_found;
logic         first_ecall_found;
logic         first_ebrk_found;
logic         first_instr_err_found;
logic         first_instr_mpuerr_found;
logic [31:0]  expected_illegal_mepc;
logic [31:0]  expected_ecall_mepc;
logic [31:0]  expected_ebrk_mepc;
logic [31:0]  expected_instr_err_mepc;
logic [31:0]  expected_instr_mpuerr_mepc;

always_ff @(posedge clk , negedge rst_ni)
  begin
    if (rst_ni == 1'b0) begin
      first_illegal_found   <= 1'b0;
      first_ecall_found     <= 1'b0;
      first_ebrk_found      <= 1'b0;
      first_instr_err_found <= 1'b0;
      first_instr_mpuerr_found <= 1'b0;
      expected_illegal_mepc <= 32'b0;
      expected_ecall_mepc   <= 32'b0;
      expected_ebrk_mepc    <= 32'b0;
      expected_instr_err_mepc <= 32'b0;
      expected_instr_mpuerr_mepc <= 32'b0;
    end
    else begin
      //TODO:OK: Update the following checks, as they fail with the new controller
      if (!first_illegal_found && ex_wb_pipe_i.instr_valid && !ctrl_fsm.kill_wb &&
        !(ex_wb_pipe_i.instr.bus_resp.err || (ex_wb_pipe_i.instr.mpu_status != MPU_OK)) &&
          ex_wb_pipe_i.illegal_insn && !id_stage_controller_debug_mode_n) begin
        first_illegal_found   <= 1'b1;
        expected_illegal_mepc <= ex_wb_pipe.pc;
      end
      if (!first_ecall_found && ex_wb_pipe_i.instr_valid && !ctrl_fsm.kill_wb &&
        !(ex_wb_pipe_i.instr.bus_resp.err || (ex_wb_pipe_i.instr.mpu_status != MPU_OK) || ex_wb_pipe_i.illegal_insn) &&
          ex_wb_pipe_i.ecall_insn && !id_stage_controller_debug_mode_n) begin
        first_ecall_found   <= 1'b1;
        expected_ecall_mepc <= ex_wb_pipe.pc;
      end
      if (!first_ebrk_found && ex_wb_pipe_i.instr_valid && !ctrl_fsm.kill_wb &&
        !(ex_wb_pipe_i.instr.bus_resp.err || (ex_wb_pipe_i.instr.mpu_status != MPU_OK) || ex_wb_pipe_i.illegal_insn || ex_wb_pipe_i.ecall_insn) &&
          ex_wb_pipe_i.ebrk_insn) begin
        first_ebrk_found   <= 1'b1;
        expected_ebrk_mepc <= ex_wb_pipe_i.pc;
      end
      
      if (!first_instr_err_found && (ex_wb_pipe_i.instr.mpu_status == MPU_OK) &&
          ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.instr.bus_resp.err && !id_stage_controller_debug_mode_n &&
          !ctrl_fsm.kill_wb ) begin
          
        first_instr_err_found   <= 1'b1;
        expected_instr_err_mepc <= ex_wb_pipe.pc;
      end
      
      if (!first_instr_mpuerr_found && ex_wb_pipe_i.instr_valid && !ctrl_fsm.kill_wb &&
          (ex_wb_pipe_i.instr.mpu_status != MPU_OK) && !id_stage_controller_debug_mode_n) begin
        first_instr_mpuerr_found   <= 1'b1;
        expected_instr_mpuerr_mepc <= ex_wb_pipe.pc;
      end
      
    end
  end

  // First mepc write for illegal instruction exception
  logic         first_cause_illegal_found;
  logic         first_cause_ecall_found;
  logic         first_cause_ebrk_found;
  logic         first_cause_instr_err_found;
  logic         first_cause_instr_mpuerr_found;
  logic [31:0]  actual_illegal_mepc;
  logic [31:0]  actual_ecall_mepc;
  logic [31:0]  actual_ebrk_mepc;
  logic [31:0]  actual_instr_err_mepc;
  logic [31:0]  actual_instr_mpuerr_mepc;

  always_ff @(posedge clk , negedge rst_ni)
    begin
      if (rst_ni == 1'b0) begin
        first_cause_illegal_found <= 1'b0;
        first_cause_ecall_found   <= 1'b0;
        first_cause_ebrk_found    <= 1'b0;
        first_cause_instr_err_found <= 1'b0;
        first_cause_instr_mpuerr_found <= 1'b0;
        actual_illegal_mepc       <= 32'b0;
        actual_ecall_mepc         <= 32'b0;
        actual_ebrk_mepc          <= 32'b0;
        actual_instr_err_mepc     <= 32'b0;
        actual_instr_mpuerr_mepc  <= 32'b0;
      end
      else begin
        if (!first_cause_illegal_found && (cs_registers_csr_cause_i == {1'b0, EXC_CAUSE_ILLEGAL_INSN}) && ctrl_fsm.csr_save_cause) begin
          first_cause_illegal_found <= 1'b1;
          actual_illegal_mepc       <= cs_registers_mepc_n;
        end
        if (!first_cause_ecall_found && (cs_registers_csr_cause_i == {1'b0, EXC_CAUSE_ECALL_MMODE}) && ctrl_fsm.csr_save_cause) begin
          first_cause_ecall_found <= 1'b1;
          actual_ecall_mepc       <= cs_registers_mepc_n;
        end
        if (!first_cause_ebrk_found && (cs_registers_csr_cause_i == {1'b0, EXC_CAUSE_BREAKPOINT}) && ctrl_fsm.csr_save_cause) begin
          first_cause_ebrk_found <= 1'b1;
          actual_ebrk_mepc       <= cs_registers_mepc_n;
        end
        if (!first_cause_instr_err_found && (cs_registers_csr_cause_i == {1'b0, EXC_CAUSE_INSTR_BUS_FAULT}) && ctrl_fsm.csr_save_cause) begin
          first_cause_instr_err_found <= 1'b1;
          actual_instr_err_mepc       <= cs_registers_mepc_n;
        end
        if (!first_cause_instr_mpuerr_found && (cs_registers_csr_cause_i == {1'b0, EXC_CAUSE_INSTR_FAULT}) && ctrl_fsm.csr_save_cause) begin
          first_cause_instr_mpuerr_found <= 1'b1;
          actual_instr_mpuerr_mepc       <= cs_registers_mepc_n;
        end
      end
    end

  // Check that mepc is updated with PC of illegal instruction
  property p_illegal_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_illegal_found && first_cause_illegal_found) |=> (expected_illegal_mepc == actual_illegal_mepc);
  endproperty

  a_illegal_mepc : assert property(p_illegal_mepc) else `uvm_error("core", "Assertion a_illegal_mepc failed")

  // Check that mepc is updated with PC of the ECALL instruction
  property p_ecall_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_ecall_found && first_cause_ecall_found) |=> (expected_ecall_mepc == actual_ecall_mepc);
  endproperty

  a_ecall_mepc : assert property(p_ecall_mepc) else `uvm_error("core", "Assertion p_ecall_mepc failed")

  // Check that mepc is updated with PC of EBRK instruction
  property p_ebrk_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_ebrk_found && first_cause_ebrk_found) |=> (expected_ebrk_mepc == actual_ebrk_mepc);
  endproperty

      
  // Check that mepc is updated with PC of instr_err instruction
  property p_instr_err_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_instr_err_found && first_cause_instr_err_found) |=> (expected_instr_err_mepc == actual_instr_err_mepc);
  endproperty

  a_instr_err_mepc : assert property(p_instr_err_mepc) else `uvm_error("core", "Assertion a_instr_err_mepc failed")

  // Check that mepc is updated with PC of mpu_err instruction
  property p_instr_mpuerr_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_instr_mpuerr_found && first_cause_instr_mpuerr_found) |=> (expected_instr_mpuerr_mepc == actual_instr_mpuerr_mepc);
  endproperty

  a_instr_mpuerr_mepc : assert property(p_instr_mpuerr_mepc) else `uvm_error("core", "Assertion a_instr_mpuerr_mepc failed")

  
  // Single Step only executes one instruction in non debug mode and next instruction WB is in debug mode
  //TODO:OK Fix, as it now fails with the new controller/pipeline signalling
  logic inst_taken;
  assign inst_taken = id_valid && id_stage_is_last;

  a_single_step :
    assert property (@(posedge clk) disable iff (!rst_ni)
                     (inst_taken && debug_single_step && ~ctrl_fsm.debug_mode)
                     ##1 inst_taken [->1]
                     |-> (ctrl_fsm.debug_mode && debug_single_step))
      else `uvm_error("core", "Assertion a_single_step failed")
  
endmodule // cv32e40x_core_sva

