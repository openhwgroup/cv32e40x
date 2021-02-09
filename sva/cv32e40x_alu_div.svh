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
// Authors    :    Michael Schaffner (schaffner@iis.ee.ethz.ch)               //
//                 Andreas Traber    (atraber@iis.ee.ethz.ch)                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the alu_div module                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import uvm_pkg::*;

initial begin : p_assertions
    assert (C_LOG_WIDTH == $clog2(C_WIDTH+1)) else `uvm_error("alu_div", "C_LOG_WIDTH must be $clog2(C_WIDTH+1)")
end

