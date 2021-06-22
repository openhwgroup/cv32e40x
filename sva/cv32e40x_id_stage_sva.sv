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
  input logic           mul_en,
  input logic           pc_set_o,
  input logic           lsu_en,
  input logic           wfi_insn,
  input logic           ebrk_insn,
  input logic           mret_insn,
  input logic           dret_insn,
  input logic           ecall_insn,
  input logic           fencei_insn,
  input logic           ex_ready_i,
  input logic           illegal_insn,
  input logic           branch_decision_i,
  input csr_opcode_e    csr_op,
  input pc_mux_e        pc_mux_o,
  input if_id_pipe_t    if_id_pipe_i,
  input id_ex_pipe_t    id_ex_pipe_o
  input logic           wb_ready_o,
  input logic           wb_valid,  
  input ctrl_fsm_t      ctrl_fsm_i,
);

  // make sure that branch decision is valid when jumping
  a_br_decision :
    assert property (@(posedge clk)
                     (id_ex_pipe_o.branch_in_ex) |-> (branch_decision_i !== 1'bx) )
      else begin `uvm_warning("id_stage", $sformatf("%t, Branch decision is X in module %m", $time)); end

    // the instruction delivered to the ID stage should always be valid
    a_valid_instr :
      assert property (@(posedge clk)
                       (if_id_pipe_i.instr_valid & (~if_id_pipe_i.illegal_c_insn)) |-> (!$isunknown(instr)) )
        else `uvm_warning("id_stage", $sformatf("%t, Instruction is valid, but has at least one X", $time));

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

      // Check that if IRQ PC update does not coincide with IRQ related CSR write
      // MIE is excluded from the check because it has a bypass.
      property p_irq_csr;
        @(posedge clk) disable iff (!rst_n)
          (pc_set_o && (pc_mux_o == PC_EXCEPTION) &&
           ((exc_pc_mux_o == EXC_PC_EXCEPTION) || (exc_pc_mux_o == EXC_PC_IRQ)) &&
           id_ex_pipe_o.csr_access && (id_ex_pipe_o.csr_op != CSR_OP_READ)) |->
                                  ((id_ex_pipe_o.alu_operand_b[11:0] != CSR_MSTATUS) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MEPC) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MCAUSE) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MTVEC));
      endproperty

      a_irq_csr : assert property(p_irq_csr) else `uvm_error("id_stage", "Assertion p_irq_csr failed")

      // Check that xret does not coincide with CSR write (to avoid using wrong return address)
      // This check is more strict than really needed; a CSR instruction would be allowed in EX as long
      // as its write action happens before the xret CSR usage
      property p_xret_csr;
        @(posedge clk) disable iff (!rst_n)
          (pc_set_o && ((pc_mux_o == PC_MRET) || (pc_mux_o == PC_DRET))) |->
                                   (!(id_ex_pipe_o.csr_access && (id_ex_pipe_o.csr_op != CSR_OP_READ)));
      endproperty

      a_xret_csr : assert property(p_xret_csr) else `uvm_error("id_stage", "Assertion a_xret_csr failed")

      generate
        if (!A_EXTENSION) begin : gen_no_a_extension_assertions

          // Check that A extension opcodes are decoded as illegal when A extension not enabled
          property p_illegal_0;
          @(posedge clk) disable iff (!rst_n) (instr[6:0] == OPCODE_AMO) |-> (illegal_insn == 'b1);
        endproperty

          a_illegal_0 : assert property(p_illegal_0) else `uvm_error("id_stage", "Assertion p_illegal_0 failed")

        end
      endgenerate

      // Check that illegal instruction has no other side effects
      property p_illegal_2;
        @(posedge clk) disable iff (!rst_n) (illegal_insn == 1'b1) |-> !(ebrk_insn || mret_insn || dret_insn ||
                                                                         ecall_insn || wfi_insn || fencei_insn ||
                                                                         alu_en || mul_en ||
                                                                         rf_we ||
                                                                         csr_op != CSR_OP_READ || lsu_en);
      endproperty

      a_illegal_2 : assert property(p_illegal_2) else `uvm_error("id_stage", "Assertion p_illegal_2 failed")
/*
  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_id)
                      |-> (!id_ready_o && !id_valid))
      else `uvm_error("id_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_id)
                      |-> (id_ready_o && !id_valid))
      else `uvm_error("id_stage", "Kill should imply ready and not valid")
*/
endmodule // cv32e40x_id_stage_sva

