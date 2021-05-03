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
  (
   input logic        clk,
   input logic        rst_n,

   input id_ex_pipe_t id_ex_pipe_i,
   input logic [31:0] csr_rdata_o,
   input logic [31:0] mie_n,
   input logic        mie_we,
   input logic [31:0] mie_bypass_o
   );

   // Store last valid rdata output
   logic [31:0] csr_rdata_last;

   always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      csr_rdata_last <= 32'h0;
    end else if (id_ex_pipe_i.csr_access) begin
      csr_rdata_last <= csr_rdata_o;
    end
  end


  // Check that mie_bypass_o equals mie_n
  a_mie_bypass : assert property (@(posedge clk) disable iff (!rst_n)
                                  (mie_we) |-> (mie_bypass_o == mie_n))
    else `uvm_error("cs_registers", "Assertion a_mie_bypass failed")

  // Check that read data is stable when csr_access is low
  a_stable_rdata: assert property (@(posedge clk) disable iff (!rst_n)
                                  (!id_ex_pipe_i.csr_access) |-> (csr_rdata_o == csr_rdata_last))

    else `uvm_error("cs_registers", "csr_rdata_o not stable while csr_access is low")
endmodule // cv32e40x_cs_registers_sva

