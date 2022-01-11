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
// Authors:        Renzo Andri - andrire@student.ethz.ch                      //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the id_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_id_stage_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
(
  input logic           clk,
  input logic           rst_n,

  input logic [31:0]    instr,
  input logic           rf_we,
  input logic           alu_en,
  input logic           div_en,
  input logic           mul_en,
  input logic           csr_en,
  input logic           sys_en,
  input logic           lsu_en,
  input logic           xif_en,
  input alu_op_a_mux_e  alu_op_a_mux_sel,
  input alu_op_b_mux_e  alu_op_b_mux_sel,
  input logic           lsu_we,
  input op_c_mux_e      op_c_mux_sel,
  input logic           sys_dret_insn,
  input logic           sys_ebrk_insn,
  input logic           sys_ecall_insn,
  input logic           sys_fencei_insn,
  input logic           sys_mret_insn,
  input logic           sys_wfi_insn,
  input logic           ex_ready_i,
  input logic           illegal_insn,
  input csr_opcode_e    csr_op,
  input if_id_pipe_t    if_id_pipe_i,
  input id_ex_pipe_t    id_ex_pipe_o,
  input logic           id_ready_o,
  input logic           id_valid_o,
  input ctrl_fsm_t      ctrl_fsm_i,
  input logic           xif_insn_accept
);

    // the instruction delivered to the ID stage should always be valid
    a_valid_instr :
      assert property (@(posedge clk)
                       (if_id_pipe_i.instr_valid & (~if_id_pipe_i.illegal_c_insn)) |-> (!$isunknown(instr)) )
        else `uvm_error("id_stage", $sformatf("%t, Instruction is valid, but has at least one X", $time));
/* todo: check and fix/remove
      // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
      // and that EX stage is ready to receive flushed instruction immediately
      property p_branch_taken_ex;
        @(posedge clk) disable iff (!rst_n) (branch_taken_ex == 1'b1) |-> ((ex_ready_i == 1'b1) &&
                                                                           (alu_en == 1'b0) &&
                                                                           (mul_en == 1'b0) &&
                                                                           (rf_we == 1'b0) &&
                                                                           (lsu_en == 1'b0));
      endproperty

      a_branch_taken_ex : assert property(p_branch_taken_ex) else `uvm_error("id_stage", "Assertion p_branch_taken_ex failed")
*/

/* todo: check and fix/remove
      // Check that if IRQ PC update does not coincide with IRQ related CSR write
      // MIE is excluded from the check because it has a bypass.
      property p_irq_csr;
        @(posedge clk) disable iff (!rst_n)
          (pc_set_o &&
           ((pc_mux_o == PC_TRAP_EXC) || (pc_mux_o == PC_TRAP_IRQ)) &&
           id_ex_pipe_o.csr_access && (id_ex_pipe_o.csr_op != CSR_OP_READ)) |->
                                  ((id_ex_pipe_o.alu_operand_b[11:0] != CSR_MSTATUS) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MEPC) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MCAUSE) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MTVEC));
      endproperty

      a_irq_csr : assert property(p_irq_csr) else `uvm_error("id_stage", "Assertion p_irq_csr failed")
*/

  // Check that illegal instruction has no other side effects
  // If XIF accepts instruction, rf_we may still be 1
  a_illegal_1 :
    assert property (@(posedge clk) disable iff (!rst_n)
      (illegal_insn == 1'b1) |-> !(alu_en || csr_en || sys_en || mul_en || div_en || lsu_en))
    else `uvm_error("id_stage", "No functional units (except for XIF) should be enabled for illegal instructions")

  a_illegal_2 :
    assert property (@(posedge clk) disable iff (!rst_n)
      (illegal_insn == 1'b1) |-> (
      (csr_op == CSR_OP_READ) &&
      (alu_op_a_mux_sel == OP_A_NONE) && (alu_op_b_mux_sel == OP_B_NONE) || (op_c_mux_sel == OP_C_NONE) &&
      !(rf_we && !xif_insn_accept)))
    else `uvm_error("id_stage", "Illegal instructions should not have side effects")

  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_id && !ctrl_fsm_i.kill_id)
                      |-> (!id_ready_o && !id_valid_o))
      else `uvm_error("id_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_id)
                      |-> (id_ready_o && !id_valid_o))
      else `uvm_error("id_stage", "Kill should imply ready and not valid")

  // Ensure that functional unit enables are one-hot (ALU and DIV both use the ALU though)
  a_functional_unit_enable_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot0({alu_en, div_en, mul_en, csr_en, sys_en, lsu_en, xif_en}))
      else `uvm_error("id_stage", "Multiple functional units enabled")

endmodule // cv32e40x_id_stage_sva

