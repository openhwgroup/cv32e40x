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

// Includes to print info about the RVFI output
// Contributors: Davide Schiavone <davide@openhwgroup.org>
//               Halfdan Bechmann <halfdan.bechmann@silabs.com>

// import cv32e40x_rvfi_pkg::*;

  integer      f;
  string       fn;
  string insn_str;

  initial begin

    wait(rst_ni == 1'b1);
    $sformat(fn, "trace_rvfi_%h.log", hart_id_i);
    f = $fopen(fn, "w");
    //$fwrite(f, " order      insn  rs1_addr  rs1_rdata  rs2_addr  rs2_rdata  rd_addr  rd_wdata    pc_rdat  mem_addr  mem_rdata  mem_wdata  TRAP  INTR\n");
    $fwrite(f, "PC        Instr     rs1_addr  rs1_rdata  rs2_addr  rs2_rdata  rd_addr  rd_wdata    mem_addr\n");

    while(1) begin

      @(posedge clk_i)

        if ( (RVFI_NRET > 1) && rvfi_valid[1] ) begin
          /*
          insn_str = $sformatf(
                          "%6d  %8h        %h  %h         %h  %h   %h  %h  PC=%h  %h  %h  %h  %h  %h",
                          rvfi_order[64+15:64],
                          rvfi_insn[2*32-1:32],
                          rvfi_rs1_addr[9:5],
                          rvfi_rs1_rdata[2*32-1:32],
                          rvfi_rs2_addr[9:5],
                          rvfi_rs2_rdata[2*32-1:32],
                          rvfi_rd_addr[9:5],
                          rvfi_rd_wdata[2*32-1:32],
                          rvfi_pc_rdata[2*32-1:32],
                          rvfi_mem_addr[2*32-1:32],
                          rvfi_mem_rdata[2*32-1:32],
                          rvfi_mem_wdata[2*32-1:32],
                          rvfi_trap[1],
                          rvfi_intr[1] );
*/
        insn_str =  $sformatf("%h  %h        %h   %h        %h   %h       %h  %h    %h",
                              rvfi_pc_rdata[2*32-1:32],
                              rvfi_insn[2*32-1:32],
                              rvfi_rs1_addr[9:5],
                              rvfi_rs1_rdata[2*32-1:32],
                              rvfi_rs2_addr[9:5],
                              rvfi_rs2_rdata[2*32-1:32],
                              rvfi_rd_addr[9:5],
                              rvfi_rd_wdata[2*32-1:32],
                              rvfi_mem_addr[2*32-1:32]
                              );

          $fwrite(f, "%s\n", insn_str);
        end // if ( (RVFI_NRET > 1) && rvfi_valid[1] )

        if( rvfi_valid[0] ) begin
          /*
          insn_str = $sformatf(
                          "%6d  %8h        %h  %h         %h  %h   %h  %h  PC=%h  %h  %h  %h  %h  %h",
                          rvfi_order[15:0],
                          rvfi_insn[31:0],
                          rvfi_rs1_addr[4:0],
                          rvfi_rs1_rdata[31:0],
                          rvfi_rs2_addr[4:0],
                          rvfi_rs2_rdata[31:0],
                          rvfi_rd_addr[4:0],
                          rvfi_rd_wdata[31:0],
                          rvfi_pc_rdata[31:0],
                          rvfi_mem_addr[31:0],
                          rvfi_mem_rdata[31:0],
                          rvfi_mem_wdata[31:0],
                          rvfi_trap[0],
                          rvfi_intr[0] );
           */
        insn_str =  $sformatf("%h  %h        %h   %h        %h   %h       %h  %h    %h",
                              rvfi_pc_rdata[31:0],
                              rvfi_insn[31:0],
                              rvfi_rs1_addr[4:0],
                              rvfi_rs1_rdata[31:0],
                              rvfi_rs2_addr[4:0],
                              rvfi_rs2_rdata[31:0],
                              rvfi_rd_addr[4:0],
                              rvfi_rd_wdata[31:0],
                              rvfi_mem_addr[31:0]
                              );
          $fwrite(f, "%s\n", insn_str);
        end // if ( rvfi_valid[0] )
    end // while (1)
  end // initial begin

