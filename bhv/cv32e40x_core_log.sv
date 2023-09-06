// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    cv32e40x_core_log.sv (cv32e40x_core simulation log)        //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Logs the following:                                        //
//                                                                            //
//                 - top level parameter settings                             //
//                 - illegal instructions                                     //
//                                                                            //
// Note:           This code was here from cv32e40x_core.sv and               //
//                 cv32e40x_controller.sv in order to remove the use of       //
//                 global defines in the RTL code.                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_core_log import cv32e40x_pkg::*;
#(
  parameter bit                         ENABLE                                  = 1,
  parameter rv32_e                      RV32                                    = RV32I,
  parameter a_ext_e                     A_EXT                                   = A_NONE,
  parameter b_ext_e                     B_EXT                                   = B_NONE,
  parameter m_ext_e                     M_EXT                                   = M,
  parameter bit                         DEBUG                                   = 1,
  parameter logic [31:0]                DM_REGION_START                         = 32'hF0000000,
  parameter logic [31:0]                DM_REGION_END                           = 32'hF0003FFF,
  parameter int                         DBG_NUM_TRIGGERS                        = 1,
  parameter int                         PMA_NUM_REGIONS                         = 0,
  parameter pma_cfg_t                   PMA_CFG[PMA_NUM_REGIONS-1:0]            = '{default:PMA_R_DEFAULT},
  parameter bit                         CLIC                                    = 0,
  parameter int unsigned                CLIC_ID_WIDTH                           = 5,
  parameter bit                         X_EXT                                   = 0,
  parameter int unsigned                X_NUM_RS                                = 2,
  parameter int unsigned                X_ID_WIDTH                              = 4,
  parameter int unsigned                X_MEM_WIDTH                             = 32,
  parameter int unsigned                X_RFR_WIDTH                             = 32,
  parameter int unsigned                X_RFW_WIDTH                             = 32,
  parameter logic [31:0]                X_MISA                                  = 32'h00000000,
  parameter logic [1:0]                 X_ECS_XS                                = 2'b00,
  parameter int unsigned                NUM_MHPMCOUNTERS                        = 1
)
(
  input logic        clk_i,
  input ex_wb_pipe_t ex_wb_pipe_i,
  input logic [31:0] mhartid_i

);

`ifndef FORMAL
  generate begin
    if (ENABLE == 1'b1) begin
      // Log top level parameter values
      initial
      begin
        $display("[cv32e40x_core]: RV32                       = %s",    RV32.name()     );
        $display("[cv32e40x_core]: A_EXT                      = %s",    A_EXT.name()    );
        $display("[cv32e40x_core]: B_EXT                      = %s",    B_EXT.name()    );
        $display("[cv32e40x_core]: M_EXT                      = %s",    M_EXT.name()    );
        $display("[cv32e40x_core]: DEBUG                      = %-1d",  DEBUG           );
        $display("[cv32e40x_core]: DM_REGION_START            = 0x%8h", DM_REGION_START );
        $display("[cv32e40x_core]: DM_REGION_END              = 0x%8h", DM_REGION_END   );
        $display("[cv32e40x_core]: DBG_NUM_TRIGGERS           = %-1d",  DBG_NUM_TRIGGERS);
        $display("[cv32e40x_core]: PMA_NUM_REGIONS            = %-2d",  PMA_NUM_REGIONS );
        for (int i_pma=0; i_pma<PMA_NUM_REGIONS; i_pma++) begin
          $display("[cv32e40x_core]: PMA_CFG[%2d].word_addr_low  = 0x%8h", i_pma, PMA_CFG[i_pma].word_addr_low);
          $display("[cv32e40x_core]: PMA_CFG[%2d].word_addr_high = 0x%8h", i_pma, PMA_CFG[i_pma].word_addr_high);
          $display("[cv32e40x_core]: PMA_CFG[%2d].main           = %-1d",  i_pma, PMA_CFG[i_pma].main);
          $display("[cv32e40x_core]: PMA_CFG[%2d].bufferable     = %-1d",  i_pma, PMA_CFG[i_pma].bufferable);
          $display("[cv32e40x_core]: PMA_CFG[%2d].cacheable      = %-1d",  i_pma, PMA_CFG[i_pma].cacheable);
          $display("[cv32e40x_core]: PMA_CFG[%2d].atomic         = %-1d",  i_pma, PMA_CFG[i_pma].atomic);
        end
        $display("[cv32e40x_core]: CLIC                       = %-1d",  CLIC             );
        $display("[cv32e40x_core]: CLIC_ID_WIDTH              = %-2d",  CLIC_ID_WIDTH    );
        $display("[cv32e40x_core]: X_EXT                      = %-1d",  X_EXT            );
        $display("[cv32e40x_core]: X_NUM_RS                   = %-1d",  X_NUM_RS         );
        $display("[cv32e40x_core]: X_ID_WIDTH                 = %-2d",  X_ID_WIDTH       );
        $display("[cv32e40x_core]: X_MEM_WIDTH                = %-3d",  X_MEM_WIDTH      );
        $display("[cv32e40x_core]: X_RFR_WIDTH                = %-2d",  X_RFR_WIDTH      );
        $display("[cv32e40x_core]: X_RFW_WIDTH                = %-2d",  X_RFW_WIDTH      );
        $display("[cv32e40x_core]: X_MISA                     = 0x%8h", X_MISA           );
        $display("[cv32e40x_core]: X_ECS_XS                   = %-1d",  X_ECS_XS         );
        $display("[cv32e40x_core]: NUM_MHPMCOUNTERS           = %-2d",  NUM_MHPMCOUNTERS );
      end

      // Log illegal instructions
      always_ff @(negedge clk_i)
      begin
        // print warning in case of decoding errors
        if (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.illegal_insn) begin
          $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, mhartid_i[3:0], ex_wb_pipe_i.pc);
        end
      end
    end
  end
  endgenerate
`endif

endmodule // cv32e40x_core_log
