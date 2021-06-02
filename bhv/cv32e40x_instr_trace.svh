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
// Engineer:       Steve Richmond - steve.richmond@silabs.com                 //
//                                                                            //
// Design Name:    cv32e40x_tracer data structures                            //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Moves the class definition for instr_trace_t out of the    //
//                 tracer module for readability and code partitioning        //
//                                                                            //
//                 Includes various enhancements to make the instr_trace_t    //
//                 class more comprehensive                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

  typedef struct {
    logic [ 5:0] addr;
    logic [31:0] value;
    bit          filled;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    int          cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    bit          compressed;
    bit          wb_bypass;
    bit          misaligned;
    bit          retire;
    bit          ebreak;
    string       str;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];
    logic        retired;

    function new ();
      str        = "";
      regs_read  = {};
      regs_write = {};
      mem_access = {};
    endfunction

    function void init(int unsigned cycles, bit[31:0] pc, bit compressed, bit[31:0] instr);
      this.simtime    = $time;
      this.cycles     = cycles;
      this.pc         = pc;
      this.compressed = compressed;
      this.instr      = instr;

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Regular opcodes
        INSTR_LUI:        this.printUInstr("lui");
        INSTR_AUIPC:      this.printUInstr("auipc");
        INSTR_JAL:        this.printUJInstr("jal");
        INSTR_JALR:       this.printIInstr("jalr");
        // BRANCH
        INSTR_BEQ:        this.printSBInstr("beq");
        INSTR_BNE:        this.printSBInstr("bne");
        INSTR_BLT:        this.printSBInstr("blt");
        INSTR_BGE:        this.printSBInstr("bge");
        INSTR_BLTU:       this.printSBInstr("bltu");
        INSTR_BGEU:       this.printSBInstr("bgeu");
        // OPIMM
        INSTR_ADDI:       this.printIInstr("addi");
        INSTR_SLTI:       this.printIInstr("slti");
        INSTR_SLTIU:      this.printIInstr("sltiu");
        INSTR_XORI:       this.printIInstr("xori");
        INSTR_ORI:        this.printIInstr("ori");
        INSTR_ANDI:       this.printIInstr("andi");
        INSTR_SLLI:       this.printIuInstr("slli");
        INSTR_SRLI:       this.printIuInstr("srli");
        INSTR_SRAI:       this.printIuInstr("srai");
        // OP
        INSTR_ADD:        this.printRInstr("add");
        INSTR_SUB:        this.printRInstr("sub");
        INSTR_SLL:        this.printRInstr("sll");
        INSTR_SLT:        this.printRInstr("slt");
        INSTR_SLTU:       this.printRInstr("sltu");
        INSTR_XOR:        this.printRInstr("xor");
        INSTR_SRL:        this.printRInstr("srl");
        INSTR_SRA:        this.printRInstr("sra");
        INSTR_OR:         this.printRInstr("or");
        INSTR_AND:        this.printRInstr("and");

        // FENCE
        INSTR_FENCE:      this.printMnemonic("fence");
        INSTR_FENCEI:     this.printMnemonic("fence.i");
        // SYSTEM (CSR manipulation)
        INSTR_CSRRW:      this.printCSRInstr("csrrw");
        INSTR_CSRRS:      this.printCSRInstr("csrrs");
        INSTR_CSRRC:      this.printCSRInstr("csrrc");
        INSTR_CSRRWI:     this.printCSRInstr("csrrwi");
        INSTR_CSRRSI:     this.printCSRInstr("csrrsi");
        INSTR_CSRRCI:     this.printCSRInstr("csrrci");
        // SYSTEM (others)
        INSTR_ECALL:      this.printMnemonic("ecall");
        INSTR_EBREAK:     this.printMnemonic("ebreak");
        INSTR_URET:       this.printMnemonic("uret");
        INSTR_MRET:       this.printMnemonic("mret");
        INSTR_WFI:        this.printMnemonic("wfi");

        INSTR_DRET:       this.printMnemonic("dret");

        // RV32M
        INSTR_MUL:        this.printRInstr("mul");
        INSTR_MUH:        this.printRInstr("mulh");
        INSTR_MULHSU:     this.printRInstr("mulhsu");
        INSTR_MULHU:      this.printRInstr("mulhu");
        INSTR_DIV:        this.printRInstr("div");
        INSTR_DIVU:       this.printRInstr("divu");
        INSTR_REM:        this.printRInstr("rem");
        INSTR_REMU:       this.printRInstr("remu");

        // RV32A
        INSTR_LR:         this.printAtomicInstr("lr.w");
        INSTR_SC:         this.printAtomicInstr("sc.w");
        INSTR_AMOSWAP:    this.printAtomicInstr("amoswap.w");
        INSTR_AMOADD:     this.printAtomicInstr("amoadd.w");
        INSTR_AMOXOR:     this.printAtomicInstr("amoxor.w");
        INSTR_AMOAND:     this.printAtomicInstr("amoand.w");
        INSTR_AMOOR:      this.printAtomicInstr("amoor.w");
        INSTR_AMOMIN:     this.printAtomicInstr("amomin.w");
        INSTR_AMOMAX:     this.printAtomicInstr("amomax.w");
        INSTR_AMOMINU:    this.printAtomicInstr("amominu.w");
        INSTR_AMOMAXU:    this.printAtomicInstr("amomaxu.w");

        // opcodes with custom decoding
        {25'b?, OPCODE_LOAD}:       this.printLoadInstr();
        {25'b?, OPCODE_STORE}:      this.printStoreInstr();
        default: this.printMnemonic("INVALID");
      endcase // unique case (instr)

    endfunction : init

    function bit is_regs_write_done();
      foreach (regs_write[i])
        if (regs_write[i].value === 'x)
          return 0;

      return 1;
    endfunction : is_regs_write_done

    function string regAddrToStr(input logic [5:0] addr);
      begin
        if (SymbolicRegs) begin // format according to RISC-V ABI
          if (addr >= 42)
            return $sformatf(" f%0d", addr-32);
          else if (addr > 32)
            return $sformatf("  f%0d", addr-32);
          else begin
            if (addr == 0)
              return $sformatf("zero");
            else if (addr == 1)
              return $sformatf("  ra");
            else if (addr == 2)
              return $sformatf("  sp");
            else if (addr == 3)
              return $sformatf("  gp");
            else if (addr == 4)
              return $sformatf("  tp");
            else if (addr >= 5 && addr <= 7)
              return $sformatf("  t%0d", addr-5);
            else if (addr >= 8 && addr <= 9)
              return $sformatf("  s%0d", addr-8);
            else if (addr >= 10 && addr <= 17)
              return $sformatf("  a%0d", addr-10);
            else if (addr >= 18 && addr <= 25)
              return $sformatf("  s%0d", addr-16);
            else if (addr >= 26 && addr <= 27)
              return $sformatf(" s%0d", addr-16);
            else if (addr >= 28 && addr <= 31)
              return $sformatf("  t%0d", addr-25);
            else
              return $sformatf("UNKNOWN %0d", addr);
          end
        end else begin
          if (addr >= 42)
            return $sformatf("f%0d", addr-32);
          else if (addr > 32)
            return $sformatf(" f%0d", addr-32);
          else if (addr < 10)
            return $sformatf(" x%0d", addr);
          else
            return $sformatf("x%0d", addr);
        end
      end
    endfunction

    function void printInstrTrace();
      mem_acc_t mem_acc;
      begin
        string insn_str;  // Accumulate writes into a single string to enable single $fwrite

        insn_str = $sformatf("%t %15d %h %h %-36s", simtime,
                                                    cycles,
                                                    pc,
                                                    instr,
                                                    str);

        foreach(regs_write[i]) begin
          if (regs_write[i].addr != 0)
            insn_str = $sformatf("%s %s=%08x", insn_str, regAddrToStr(regs_write[i].addr), regs_write[i].value);
        end

        foreach(regs_read[i]) begin
          if (regs_read[i].addr != 0)
            insn_str = $sformatf("%s %s:%08x", insn_str, regAddrToStr(regs_read[i].addr), regs_read[i].value);
        end

        if (mem_access.size() > 0) begin
          mem_acc = mem_access.pop_front();

          insn_str = $sformatf("%s  PA:%08x", insn_str, mem_acc.addr);
        end

        $fwrite(f, "%s\n", insn_str);
      end
    endfunction

    function void printMnemonic(input string mnemonic);
      begin
        str = {compressed ? "c." : "", mnemonic};
      end
    endfunction // printMnemonic

    function void printRInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printRInstr

    function void printR1Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d", mnemonic, rd, rs1);
      end
    endfunction // printR1Instr

    function void printR3Instr(input string mnemonic);
      begin
        regs_read.push_back('{rd, rs3_value, 0});
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printR3Instr

    function void printF3Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_read.push_back('{rs4, rs3_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32, rs4-32);
      end
    endfunction // printF3Instr

    function void printF2Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32);
      end
    endfunction // printF2Instr

    function void printF2IInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, f%0d, f%0d", mnemonic, rd, rs1-32, rs2-32);
      end
    endfunction // printF2IInstr

    function void printFInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d", mnemonic, rd-32, rs1-32);
      end
    endfunction // printFInstr

    function void printFIInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, f%0d", mnemonic, rd, rs1-32);
      end
    endfunction // printFIInstr

    function void printIFInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, x%0d", mnemonic, rd-32, rs1);
      end
    endfunction // printIFInstr

    function void printClipInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $unsigned(imm_clip_type));
      end
    endfunction // printRInstr

    function void printIInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
      end
    endfunction // printIInstr

    function void printIuInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, 5'(imm_i_type));
      end
    endfunction // printIuInstr

    function void printUInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
      end
    endfunction // printUInstr

    function void printUJInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_write.push_back('{rd, 'x, 0});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
      end
    endfunction // printUJInstr

    function void printSBInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        str =  $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printSBallInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rs1, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printCSRInstr(input string mnemonic);
      logic [11:0] csr;
      begin
        csr = instr[31:20];

        regs_write.push_back('{rd, 'x, 0});

        if (instr[14] == 1'b0) begin
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
        end else begin
          str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
        end
      end
    endfunction // printCSRInstr

    function void printAtomicInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});
        if (instr[31:27] == AMO_LR) begin
          // Do not print rs2 for load-reserved
          str = $sformatf("%-16s x%0d, (x%0d)", mnemonic, rd, rs1);
        end else begin
          str = $sformatf("%-16s x%0d, x%0d, (x%0d)", mnemonic, rd, rs2, rs1);
        end
      end
    endfunction // printAtomicInstr

    function void printLoadInstr();
      string mnemonic;
      logic [2:0] size;
      begin
        // detect reg-reg load and find size
        size = instr[14:12];
        if (instr[14:12] == 3'b111)
          size = instr[30:28];

        case (size)
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b011,
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase
        mnemonic = {compressed ? "c." : "", mnemonic};

        regs_write.push_back('{rd, 'x, 0});

        if (instr[14:12] != 3'b111) begin
          // regular load
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
        end else begin
          // reg-reg load
          regs_read.push_back('{rs2, rs2_value,0});
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
        end
      end
    endfunction

    function void printStoreInstr();
      string mnemonic;
      begin

        case (instr[13:12])
          2'b00:  mnemonic = "sb";
          2'b01:  mnemonic = "sh";
          2'b10:  mnemonic = "sw";
          2'b11: begin
            printMnemonic("INVALID");
            return;
          end
        endcase
        mnemonic = {compressed ? "c." : "", mnemonic};

        if (instr[14] == 1'b0) begin
          // regular store
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end else begin
          // reg-reg store
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs3, rs3_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
        end
      end
    endfunction // printSInstr

    function void printMulInstr();
      string mnemonic;
      string str_suf;
      string str_imm;
      string str_asm;
      begin

        // always read rs1 and rs2 and write rd
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});

        if (instr[12])
          regs_read.push_back('{rd, rs3_value, 0});

        case ({instr[31:30], instr[14]})
          3'b000: str_suf = "u";
          3'b001: str_suf = "uR";
          3'b010: str_suf = "hhu";
          3'b011: str_suf = "hhuR";
          3'b100: str_suf = "s";
          3'b101: str_suf = "sR";
          3'b110: str_suf = "hhs";
          3'b111: str_suf = "hhsR";
        endcase

        mnemonic = "p.mul";

        str_asm = $sformatf("%s%s", mnemonic, str_suf);

        str = $sformatf("%-16s x%0d, x%0d, x%0d", str_asm, rd, rs1, rs2);
      end
    endfunction

  endclass
