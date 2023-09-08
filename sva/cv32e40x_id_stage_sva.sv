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
#(
  parameter rv32_e RV32   = RV32I
)
(
  input logic           clk,
  input logic           rst_n,
  input logic [1:0]     rf_re,
  input rf_addr_t       rf_raddr_o[2],
  input logic           rf_we,
  input logic           rf_we_dec,
  input rf_addr_t       rf_waddr,
  input logic           alu_en,
  input logic           div_en,
  input logic           mul_en,
  input logic           csr_en,
  input logic           sys_en,
  input logic           lsu_en,
  input logic           xif_en,
  input alu_op_a_mux_e  alu_op_a_mux_sel,
  input alu_op_b_mux_e  alu_op_b_mux_sel,
  input op_c_mux_e      op_c_mux_sel,
  input logic           ex_ready_i,
  input logic           illegal_insn,
  input csr_opcode_e    csr_op,
  input id_ex_pipe_t    id_ex_pipe_o,
  input logic           id_ready_o,
  input logic           id_valid_o,
  input ctrl_fsm_t      ctrl_fsm_i,
  input logic           xif_insn_accept,
  input logic [31:0]    jalr_fw,
  input logic [31:0]    operand_a_fw,
  input logic           alu_jmpr,
  input logic [31:0]    jmp_target_o,
  input logic           jmp_taken_id_ctrl_i
);

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

  // Assert that jalr_fw has the same value as operand_a_fw when a jump is taken
  // Only checking for JALR, as regular JAL do not use any RF or bypass operands for the jump target.
  // Checked because RVFI is using operand_a_fw only, even for JALR instructions. With this assert proven,
  // there is no need to mux in jalr_fw inside RVFI.
  a_jalr_fw_match :
    assert property (@(posedge clk) disable iff (!rst_n)
                      jmp_taken_id_ctrl_i && alu_jmpr
                      |->
                      (jalr_fw == operand_a_fw))
      else `uvm_error("id_stage", "jalr_fw does not match operand_a_fw")

  // Assert stable jump target for a jump instruction that stays multiple cycles in ID
  // Target must remain stable until instruction exits ID (id_valid && ex_ready, or
  // instructions is killed.
  property p_jmp_target_stable;
    logic [31:0] jmp_target;
    @(posedge clk) disable iff (!rst_n)
    (jmp_taken_id_ctrl_i && !ctrl_fsm_i.kill_id, jmp_target=jmp_target_o)
    |->
    (jmp_target == jmp_target_o) until_with ((id_valid_o && ex_ready_i) || ctrl_fsm_i.kill_id);
  endproperty

  a_jmp_target_stable: assert property (p_jmp_target_stable)
    else `uvm_error("id_stage", "Jump target not stable")


    generate
      if(RV32 == RV32E) begin: a_rv32e

        a_rf_we_illegal :
          assert property (@(posedge clk) disable iff (!rst_n)
                           rf_we_dec |-> (rf_waddr < 16))
            else `uvm_error("decoder", "Write to GPR > 15")

        a_rf_re_illegal_0 :
          assert property (@(posedge clk) disable iff (!rst_n)
                           rf_re[0] |-> (rf_raddr_o[0] < 16))
            else `uvm_error("decoder", "Read from to GPR > 15")

        a_rf_re_illegal_1 :
          assert property (@(posedge clk) disable iff (!rst_n)
                           rf_re[1] |-> (rf_raddr_o[1] < 16))
            else `uvm_error("decoder", "Read from GPR > 15")

      end
    endgenerate

endmodule // cv32e40x_id_stage_sva

