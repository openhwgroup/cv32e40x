// Copyright (c) 2022 OpenHW Group
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

// CV32E40X RVFI data OBI interface (aligns data OBI signals to WB timing)
//
// Contributors: Arjan Bink <arjan.bink@silabs.com>

module cv32e40x_rvfi_data_obi import cv32e40x_pkg::*; import cv32e40x_rvfi_pkg::*;
(
  input  logic                          clk,
  input  logic                          rst_n
);

  // DEPTH of the instruction buffer (at least depth of alignment buffer)
  localparam DEPTH = 4;                                                         // Needs to be power of 2 (due to used pointer arithmetic)
  localparam int unsigned PTR_WIDTH = $clog2(DEPTH);

endmodule
