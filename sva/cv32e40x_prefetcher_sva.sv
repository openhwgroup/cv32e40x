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
// Design Name:    Prefetcher Controller SVA                                  //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    SV Properties, Assertions, etc, for the CV32E40P           //
//                 Prefetch Controller.                                       //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_prefetcher_sva
(
  input  logic        clk,
  input  logic        rst_n,

  // Fetch stage interface
  input  logic        fetch_branch_i,                 // Taken branch
  input  logic [31:0] fetch_branch_addr_i,            // Taken branch address (only valid when branch_i = 1)

  // Transaction request interface
  input  logic        trans_valid_o,            // Transaction request valid (to bus interface adapter)
  input  logic        trans_ready_i,            // Transaction request ready (transaction gets accepted when trans_valid_o and trans_ready_i are both 1)
  input  logic [31:0] trans_addr_o,             // Transaction address (only valid when trans_valid_o = 1). No stability requirements.

  // Fetch interface is ready/valid
  input  logic        fetch_ready_o,
  input  logic        fetch_valid_i

  
);

  import uvm_pkg::*; // needed for the UVM messaging service (`uvm_error(), etc.)

 
 
  // Check that we only assert trans_valid when fetch_valid is high (R-6=)
  property p_trans_valid;
     @(posedge clk) disable iff (!rst_n) (trans_valid_o) |-> (fetch_valid_i);
  endproperty

  a_trans_valid:
    assert property(p_trans_valid)
    else
      `uvm_error("Prefetcher SVA",
                 $sformatf("trans_valid_o active when fetch_valid_i is not"))

  // Check that we output branch address correctly (R-7)
  property p_branch_addr;
    @(posedge clk) disable iff (!rst_n) (fetch_branch_i) |-> (trans_addr_o == fetch_branch_addr_i);
  endproperty
             
  a_branch_addr:
    assert property(p_branch_addr)
    else
      `uvm_error("Prefetcher SVA",
                $sformatf("branch address not propagated to trans_addr_o correctly"))

  // Check that fetch_branch_addr_i is word aligned (R-8)
  property p_fetch_branch_addr_aligned;
    @(posedge clk) disable iff (!rst_n) (fetch_branch_addr_i[1:0] == 2'b00);
  endproperty
                            
  a_fetch_branch_addr_aligned:
    assert property(p_fetch_branch_addr_aligned)
    else
      `uvm_error("Prefetcher SVA",
                $sformatf("fetch_branch_addr_i is not word aligned."))

  // Check that trans_addr_o is word aligned (R-8)
  property p_trans_addr_aligned;
    @(posedge clk) disable iff (!rst_n) (trans_addr_o[1:0] == 2'b00);
  endproperty
                            
  a_trans_addr_aligned:
    assert property(p_trans_addr_aligned)
    else
      `uvm_error("Prefetcher SVA",
                $sformatf("trans_addr_o is not word aligned."))


  // Check that we acknowlede a fetch_valid when trans_ready high (R-9)
  property p_fetch_ready;
    @(posedge clk) disable iff (!rst_n) (trans_ready_i && trans_valid_o) |-> (fetch_ready_o == 1'b1);
  endproperty
                           
  a_fetch_ready:
    assert property(p_fetch_ready)
    else
      `uvm_error("Prefetcher SVA",
                $sformatf("fetch_ready_o not set when trans_ready_i && trans_valid_o."))
endmodule: cv32e40x_prefetcher_sva
