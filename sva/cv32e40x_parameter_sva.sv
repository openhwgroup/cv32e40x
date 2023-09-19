// Copyright 2023 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    Assertions for top level parameters                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_parameter_sva import cv32e40x_pkg::*;
  #(
    parameter int          PMA_NUM_REGIONS              = 0,
    parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT},
    parameter logic [31:0] DM_REGION_START              = 32'hF0000000,
    parameter logic [31:0] DM_REGION_END                = 32'hF0003FFF,
    parameter int          DBG_NUM_TRIGGERS             = 1,
    parameter int unsigned CLIC_ID_WIDTH                = 5,
    parameter int unsigned NUM_MHPMCOUNTERS             = 1
    )
  (
   input logic clk_i,
   input logic rst_ni
   );

  a_param_pma_num_regions :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= PMA_NUM_REGIONS) && (PMA_NUM_REGIONS <= 16))
    else $fatal(0, "Invalid PMA_NUM_REGIONS");

  generate for (genvar i = 0; i < PMA_NUM_REGIONS; i++)
    begin : a_pma_no_illegal_configs

      if (!PMA_CFG[i].main) begin
        a_param_pma_io_noncacheable :
          assert property (@(posedge clk_i) disable iff (!rst_ni)
                           !PMA_CFG[i].cacheable)
            else $fatal(0, "Invalid PMA region configuration: cacheable I/O region");
      end

      a_param_pma_addr_range :
        assert property (@(posedge clk_i) disable iff (!rst_ni)
                         PMA_CFG[i].word_addr_high >= PMA_CFG[i].word_addr_low)
        else $fatal(0, "Invalid PMA region boundaries");

    end
  endgenerate

  a_param_dm_region :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     DM_REGION_END > DM_REGION_START)
    else $fatal(0, "Invalid combination of DM_REGION_START and DM_REGION_END");

  a_param_dbg_num_triggers :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= DBG_NUM_TRIGGERS) && (DBG_NUM_TRIGGERS <= 4))
    else $fatal(0, "Invalid DBG_NUM_TRIGGERS");

  a_param_clic_id_width :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (1 <= CLIC_ID_WIDTH) && (CLIC_ID_WIDTH <= 10))
    else $fatal(0, "Invalid CLIC_ID_WIDTH");

  a_param_num_mhpmcounters :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= NUM_MHPMCOUNTERS) && (NUM_MHPMCOUNTERS <= 29))
    else $fatal(0, "Invalid NUM_MHPMCOUNTERS");

endmodule
