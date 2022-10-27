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
// Authors:        Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    RTL assertions for the cs_registers module                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_cs_registers_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
#(
    parameter bit SMCLIC = 0
  )

  (
   input logic        clk,
   input logic        rst_n,
   input ctrl_fsm_t   ctrl_fsm_i,
   input id_ex_pipe_t id_ex_pipe_i,
   input ex_wb_pipe_t ex_wb_pipe_i,
   input logic [31:0] csr_rdata_o,
   input logic        csr_we_int,
   input logic [1:0]  mtvec_mode_o,
   input logic        wb_valid_i,
   input logic        mnxti_we,
   input logic        mintstatus_we,
   input logic        mcause_we,
   input logic [31:0] clic_pa_o,
   input logic        clic_pa_valid_o,
   input mintstatus_t mintstatus_rdata,
   input privlvl_t    priv_lvl_n,
   input privlvl_t    priv_lvl_rdata,
   input logic [31:0] mscratch_rdata,
   input mcause_t     mcause_rdata,
   csr_num_e          csr_waddr,
   input logic        mscratch_we,
   input logic        instr_valid,
   input csr_opcode_e csr_op

   );


   // CSR file shall not be written when WB is halted or killed
  a_csr_halt_kill:
  assert property (@(posedge clk) disable iff (!rst_n)
                  (ctrl_fsm_i.kill_wb || ctrl_fsm_i.halt_wb)
                  |-> !csr_we_int)
    else `uvm_error("wb_stage", "Register file written while WB is halted or killed")

  if (SMCLIC) begin
    // Assert that mtvec[1:0] are always 2'b11
    a_mtvec_mode_clic:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> mtvec_mode_o == 2'b11)
      else `uvm_error("cs_registers", "mtvec_mode is not 2'b11 in CLIC mode")

    // Accesses to MNXTI are stalled in EX if there is a LSU instruction in WB.
    // Thus no mnxti should be in WB (clic_pa_valid_o) the cycle after an LSU instruction
    // is done in WB.
    property p_no_mnxti_after_lsu;
      @(posedge clk) disable iff (!rst_n)
      (  wb_valid_i && ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid
        |=>
        !clic_pa_valid_o);
    endproperty;

    a_no_mnxti_after_lsu: assert property(p_no_mnxti_after_lsu)
      else `uvm_error("cs_registers", "Mnxti should not we in WB the cycle after an LSU instruction");


    // Check that horizontal traps keep the current interrupt level
    property p_htrap_interrupt_level;
      @(posedge clk) disable iff (!rst_n)
      (  ctrl_fsm_i.csr_save_cause && !ctrl_fsm_i.debug_csr_save && !ctrl_fsm_i.csr_cause.irq && (priv_lvl_n == priv_lvl_rdata)
         |=>
         $stable(mintstatus_rdata.mil));

    endproperty;

    a_htrap_interrupt_level: assert property(p_htrap_interrupt_level)
      else `uvm_error("cs_registers", "Horizontal trap taken caused interrupt level to change");

    // Check that mscratch do not update due to mscratchcsw if the conditions are not right
    property p_mscratchcsw_mscratch;
      @(posedge clk) disable iff (!rst_n)
      (  ex_wb_pipe_i.csr_en && (csr_waddr == CSR_MSCRATCHCSW) && (mcause_rdata.mpp == PRIV_LVL_M)
        |=> $stable(mscratch_rdata));
    endproperty;

    a_mscratchcsw_mscratch: assert property(p_mscratchcsw_mscratch)
      else `uvm_error("cs_registers", "Mscratch not stable after mscratwchsw with mpp=M");

    // Check that mscratch do not update due to mscratchcswl if the conditions are not right
    property p_mscratchcswl_mscratch;
      @(posedge clk) disable iff (!rst_n)
      (  ex_wb_pipe_i.csr_en && (csr_waddr == CSR_MSCRATCHCSWL) && !((mcause_rdata.mpil == '0) != (mintstatus_rdata.mil == '0))
        |=> $stable(mscratch_rdata));
    endproperty;

    a_mscratchcswl_mscratch: assert property(p_mscratchcswl_mscratch)
      else `uvm_error("cs_registers", "Mscratch not stable after mscratwchswl");

    // Check that mscratch is written by mscratchcswl when the conditions are right
    property p_mscratchcswl_mscratch_we;
      @(posedge clk) disable iff (!rst_n)
      (  ex_wb_pipe_i.csr_en && (csr_waddr == CSR_MSCRATCHCSWL) && ((mcause_rdata.mpil == '0) != (mintstatus_rdata.mil == '0))
         && (csr_op != CSR_OP_READ) && instr_valid
        |-> mscratch_we);
    endproperty;

    a_mscratchcswl_mscratch_we: assert property(p_mscratchcswl_mscratch_we)
      else `uvm_error("cs_registers", "Mscratch not written by mscratchcswl");

  end

  // Check that no csr instruction can be in WB during sleep when ctrl_fsm.halt_limited_wb is set
  property p_halt_limited_wb;
    @(posedge clk) disable iff (!rst_n)
    (  ctrl_fsm_i.halt_limited_wb |-> !(ex_wb_pipe_i.csr_en && ex_wb_pipe_i.instr_valid));
  endproperty;

  a_halt_limited_wb: assert property(p_halt_limited_wb)
    else `uvm_error("cs_registers", "CSR in WB while halt_limited_wb is set");

  // Check that mcause is not written when an mret or dret is in WB
  property p_mret_dret_wb_mcause_write;
    @(posedge clk) disable iff (!rst_n)
    (  (ctrl_fsm_i.csr_restore_mret || ctrl_fsm_i.csr_restore_dret) && !ctrl_fsm_i.csr_clear_minhv |-> !mcause_we);
  endproperty;

  a_mret_dret_wb_mcause_write: assert property(p_mret_dret_wb_mcause_write)
    else `uvm_error("cs_registers", "mcause written when MRET or DRET is in WB.");

  // Check csr_clear_minhv cannot happen at the same time as csr_save_cause or csr_restore_dret (would cause mcause_we conflict)
  property p_minhv_unique;
    @(posedge clk) disable iff (!rst_n)
    (  ctrl_fsm_i.csr_clear_minhv -> !(ctrl_fsm_i.csr_save_cause || ctrl_fsm_i.csr_restore_dret));
  endproperty;

  a_minhv_unique: assert property(p_minhv_unique)
    else `uvm_error("cs_registers", "csr_save_cause at the same time as csr_clear_minhv.");


  // Check EX is empty or contains last part of mret when minhv is cleared
  property p_ex_empty_minhv_clear;
    @(posedge clk) disable iff (!rst_n)
    (  ctrl_fsm_i.csr_clear_minhv
       -> !id_ex_pipe_i.instr_valid       // No valid instruction in EX
       or
          (id_ex_pipe_i.instr_valid && id_ex_pipe_i.sys_en && id_ex_pipe_i.sys_mret_insn && id_ex_pipe_i.last_op)); // Last part of hardened mret in EX
  endproperty;

  a_ex_empty_minhv_clear: assert property(p_ex_empty_minhv_clear)
    else `uvm_error("cs_registers", "EX not empty when csr_clear_minhv is active.");

  // Check WB is empty or contains any part of mret when minhv is cleared
  property p_wb_empty_minhv_clear;
    @(posedge clk) disable iff (!rst_n)
    (  ctrl_fsm_i.csr_clear_minhv
        -> !ex_wb_pipe_i.instr_valid       // No valid instruction in WB
        or
          (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_mret_insn)); // Any part of hardened mret in WB
  endproperty;

  a_wb_empty_minhv_clear: assert property(p_wb_empty_minhv_clear)
    else `uvm_error("cs_registers", "WB not empty when csr_clear_minhv is active.");
endmodule

