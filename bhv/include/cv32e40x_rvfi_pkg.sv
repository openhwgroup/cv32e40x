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

package cv32e40x_rvfi_pkg;

  typedef struct packed {
    logic        rvfi_valid;
    logic [63:0] rvfi_order;
    logic [31:0] rvfi_insn;
    logic        rvfi_trap;
    logic        rvfi_halt;
    logic        rvfi_intr;
    logic [ 4:0] rvfi_rs1_addr;
    logic [ 4:0] rvfi_rs2_addr;
    logic [ 4:0] rvfi_rs3_addr;
    logic [31:0] rvfi_rs1_rdata;
    logic [31:0] rvfi_rs2_rdata;
    logic [31:0] rvfi_rs3_rdata;
    logic [ 4:0] rvfi_rd_addr;
    logic [31:0] rvfi_rd_wdata;
    logic [31:0] rvfi_pc_rdata;
    logic [31:0] rvfi_pc_wdata;
    logic [31:0] rvfi_mem_addr;
    logic [ 3:0] rvfi_mem_rmask;
    logic [ 3:0] rvfi_mem_wmask;
    logic [31:0] rvfi_mem_rdata;
    logic [31:0] rvfi_mem_wdata;
    logic [31:0] rvfi_csr_mstatus_rmask;
    logic [31:0] rvfi_csr_mstatus_wmask;
    logic [31:0] rvfi_csr_mstatus_rdata;
    logic [31:0] rvfi_csr_mstatus_wdata;
  } rvfi_instr_t;

  typedef struct packed {
    logic        valid;
    logic [63:0] order;
    logic [31:0] pc_wdata;
  } rvfi_intr_t;

endpackage // cv32e40x_rvfi_pkg
  
