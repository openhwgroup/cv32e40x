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


  integer      f;
  string insn_str;

  initial begin

    wait(rst_ni == 1'b1);
    f = $fopen ("trace_rvfi.log", "w");
    $fwrite(f, "PC        Instr     rs1_addr  rs1_rdata  rs2_addr  rs2_rdata  rd_addr  rd_wdata    mem_addr mem_rmask mem_wmask mem_rdata mem_wdata\n");

    while(1) begin

      @(posedge clk_i)

        if ( rvfi_valid ) begin
          insn_str =  $sformatf("%h  %h        %h   %h        %h   %h       %h  %h    %h         %h         %h  %h  %h",
                                rvfi_pc_rdata ,
                                rvfi_insn     ,
                                rvfi_rs1_addr ,
                                rvfi_rs1_rdata,
                                rvfi_rs2_addr ,
                                rvfi_rs2_rdata,
                                rvfi_rd_addr  ,
                                rvfi_rd_wdata ,
                                rvfi_mem_addr ,
                                rvfi_mem_rmask,
                                rvfi_mem_wmask,
                                rvfi_mem_rdata,
                                rvfi_mem_wdata
                                );
          $fwrite(f, "%s\n", insn_str);
        end // if ( rvfi_valid )

    end // while (1)
  end // initial begin

