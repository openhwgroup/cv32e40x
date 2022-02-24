// Copyright 2022 Silicon Labs, Inc.
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
// Description:    RVFI tracer.                                               // 
//                 Parses itb file and generates trace based on retired       //
//                 instruction address                                        //
//                 The path of the .itb file is given using the plusarg       //
//                 defined by ITB_PLUSARG                                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module rvfi_sim_trace
  #(parameter string ITB_PLUSARG = "itb_file")
  (
   input logic        rvfi_valid,
   input logic [31:0] rvfi_pc_rdata
   );

  typedef struct      {
    bit [32*16-1:0]  c_file;
    bit [32*16-1:0]  c_func;
    int              c_line;
    logic [31:0]     addr;
    logic [31:0]     mcode;
    bit [32*16-1:0]  asm;
  } trace_t;

  localparam trace_t TRACE_UNKNOWN = '{c_func : "NA",
                                       c_file : "NA",
                                       c_line : -1,
                                       addr   : 'x,
                                       mcode  : 'x,
                                       asm    : "NA"};
  
  trace_t itrace, tmp_trace;
  trace_t imap[int];
  int                 file;
  int                 elements_found, asmlen;
  string              filename, line;
  string              asms[5];
  bit                 itb_file_ok;

  // Populate itrace based on retired instruction
  always_comb begin
    if (rvfi_valid && ^rvfi_pc_rdata !== 1'bx && imap.exists(rvfi_pc_rdata)) begin
      // Pick trace from instruction map
      itrace = imap[rvfi_pc_rdata];
    end
    else begin
      itrace = TRACE_UNKNOWN;
    end
  end

  // Parse the listing file
  initial begin

    $display("RISC-V Trace: Using itb path defined by plusarg: %s", ITB_PLUSARG);

    if (!$value$plusargs({ITB_PLUSARG,"=%s"}, filename)) begin
      $display("RISC-V Trace: No instruction table file found.");
    end
    else begin

      file = $fopen(filename, "r");

      if (file == 0) begin
        $display("RISC-V Trace: Failed to open instruction table file %s", filename);
        itb_file_ok = 1'b0;
      end
      else begin

        $display("RISC-V Trace: Loading instruction table file %s", filename);
        itb_file_ok = 1'b1;

        // Iterate through itb file
        while ($fgets(line, file)) begin
          // Skip comments
          if(line[0] != "#") begin

            // Search for expected pattern in line
            elements_found = $sscanf(line, "%d %s %s %d %h %d %s %s %s %s %s",
                                     tmp_trace.addr, tmp_trace.c_func, tmp_trace.c_file, tmp_trace.c_line, tmp_trace.mcode, asmlen, asms[0], asms[1], asms[2], asms[3], asms[4]);

            if (elements_found > 6) begin
              // Fetch assembly instruction
              for (int i=0; i < asmlen; i++) begin
                if(asms[i] == "#") break; // Disregard comments

                // Concatenate assembly instruction
                $cast(tmp_trace.asm,  $sformatf("%s %s", tmp_trace.asm, asms[i]));

              end

              imap[tmp_trace.addr] = tmp_trace;
              tmp_trace.asm = "";
            end
          end
        end
      end
      $fclose(file);
      $display("RISC-V Trace: Loaded %d instructions.", imap.size());
    end
  end

endmodule
