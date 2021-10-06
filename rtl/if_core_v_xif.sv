/*
 Copyright 2021 TU Wien

 This file, and derivatives thereof are licensed under the
 Solderpad License, Version 2.0 (the "License");
 Use of this file means you agree to the terms and conditions
 of the license and are in full compliance with the License.
 You may obtain a copy of the License at

 https://solderpad.org/licenses/SHL-2.0/

 Unless required by applicable law or agreed to in writing, software
 and hardware implementations thereof
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    CORE-V XIF eXtension Interface                             //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Definition of the CORE-V XIF eXtension Interface.          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

interface if_core_v_xif import cv32e40x_pkg::*;
#(
  parameter int          X_NUM_RS        =  2,  // Number of register file read ports that can be used by the eXtension interface
  parameter int          X_MEM_WIDTH     =  32, // Memory access width for loads/stores via the eXtension interface
  parameter int          X_RFR_WIDTH     =  32, // Register file read access width for the eXtension interface
  parameter int          X_RFW_WIDTH     =  32, // Register file write access width for the eXtension interface
  parameter logic [31:0] X_MISA          =  '0  // MISA extensions implemented on the eXtension interface
);

  localparam int XLEN = 32;
  localparam int FLEN = 32;

  typedef struct packed {
    logic [          15:0] instr; // Offloaded compressed instruction
    logic [           1:0] mode;  // Privilege level
    logic [X_ID_WIDTH-1:0] id;    // Identification number of the offloaded compressed instruction
  } x_compressed_req_t;

  typedef struct packed {
    logic [31:0] instr;   // Uncompressed instruction
    logic        accept;  // Is the offloaded compressed instruction (id) accepted by the coprocessor?
  } x_compressed_resp_t;

  typedef struct packed {
    logic [           31:0]               instr;     // Offloaded instruction
    logic [            1:0]               mode;      // Privilege level
    logic [X_ID_WIDTH -1:0]               id;        // Identification of the offloaded instruction
    logic [X_RFR_WIDTH-1:0][X_NUM_RS-1:0] rs;        // Register file source operands for the offloaded instruction
    logic [X_NUM_RS   -1:0]               rs_valid;  // Validity of the register file source operand(s)
    logic [FLEN       -1:0][X_NUM_RS-1:0] frs;       // Floating-point register file source operands for the offloaded instruction
    logic [X_NUM_FRS  -1:0]               frs_valid; // Validity of the floating-point register file source operand(s)
  } x_issue_req_t;

  typedef struct packed {
    logic accept;     // Is the offloaded instruction (id) accepted by the coprocessor?
    logic writeback;  // Will the coprocessor perform a writeback in the core to rd?
    logic float;      // Qualifies whether a writeback is to the floating-point register file or to integer register file?
    logic dualwrite;  // Will the coprocessor perform a dual writeback in the core to rd and rd+1?
    logic dualread;   // Will the coprocessor require dual reads from rs1\rs2\rs3 and rs1+1\rs2+1\rs3+1?
    logic loadstore;  // Is the offloaded instruction a load/store instruction?
    logic exc;        // Can the offloaded instruction possibly cause a synchronous exception in the coprocessor itself?
  } x_issue_resp_t;

  typedef struct packed {
    logic [X_ID_WIDTH-1:0] id;          // Identification of the offloaded instruction
    logic                  commit_kill; // Shall an offloaded instruction be killed?
  } x_commit_t;

  typedef struct packed {
    logic [X_ID_WIDTH -1:0] id;       // Identification of the offloaded instruction
    logic [           31:0] addr;     // Virtual address of the memory transaction
    logic [            1:0] mode;     // Privilege level
    logic                   we;       // Write enable of the memory transaction
    logic [            1:0] size;     // Size of the memory transaction
    logic [X_MEM_WIDTH-1:0] wdata;    // Write data of a store memory transaction
    logic                   last;     // Is this the last memory transaction for the offloaded instruction?
    logic                   spec;     // Is the memory transaction speculative?
  } x_mem_req_t;

  typedef struct packed {
    logic       exc;      // Did the memory request cause a synchronous exception?
    logic [5:0] exccode;  // Exception code
  } x_mem_resp_t;

  typedef struct packed {
    logic [X_ID_WIDTH -1:0] id;     // Identification of the offloaded instruction
    logic [X_MEM_WIDTH-1:0] rdata;  // Read data of a read memory transaction
    logic                   err;    // Did the instruction cause a bus error?
  } x_mem_result_t;

  typedef struct packed {
    logic [X_ID_WIDTH -   1:0] id;      // Identification of the offloaded instruction
    logic [X_RFW_WIDTH-   1:0] data;    // Register file write data value(s)
    logic [               4:0] rd;      // Register file destination address(es)
    logic [X_RFW_WIDTH-XLEN:0] we;      // Register file write enable(s)
    logic                      float;   // Floating-point register file or integer register file?
    logic                      exc;     // Did the instruction cause a synchronous exception?
    logic [               5:0] exccode; // Exception code
  } x_result_t;


  // Compressed interface
  logic               x_compressed_valid;
  logic               x_compressed_ready;
  x_compressed_req_t  x_compressed_req;
  x_compressed_resp_t x_compressed_resp;

  // Issue interface
  logic               x_issue_valid;
  logic               x_issue_ready;
  x_issue_req_t       x_issue_req;
  x_issue_resp_t      x_issue_resp;

  // Commit interface
  logic               x_commit_valid;
  x_commit_t          x_commit;

  // Memory (request/response) interface
  logic               x_mem_valid;
  logic               x_mem_ready;
  x_mem_req_t         x_mem_req;
  x_mem_resp_t        x_mem_resp;

  // Memory result interface
  logic               x_mem_result_valid;
  x_mem_result_t      x_mem_result;

  // Result interface
  logic               x_result_valid;
  logic               x_result_ready;
  x_result_t          x_result;


  // Port directions for host CPU
  modport cpu (
    output x_compressed_valid,
    input  x_compressed_ready,
    output x_compressed_req,
    input  x_compressed_resp,
    output x_issue_valid,
    input  x_issue_ready,
    output x_issue_req,
    input  x_issue_resp,
    output x_commit_valid,
    output x_commit,
    input  x_mem_valid,
    output x_mem_ready,
    input  x_mem_req,
    output x_mem_resp,
    output x_mem_result_valid,
    output x_mem_result,
    input  x_result_valid,
    output x_result_ready,
    input  x_result
  );

  // Port directions for extension
  modport coproc (
    input  x_compressed_valid,
    output x_compressed_ready,
    input  x_compressed_req,
    output x_compressed_resp,
    input  x_issue_valid,
    output x_issue_ready,
    input  x_issue_req,
    output x_issue_resp,
    input  x_commit_valid,
    input  x_commit,
    output x_mem_valid,
    input  x_mem_ready,
    output x_mem_req,
    input  x_mem_resp,
    input  x_mem_result_valid,
    input  x_mem_result,
    output x_result_valid,
    input  x_result_ready,
    output x_result
  );

endinterface : if_core_v_xif
