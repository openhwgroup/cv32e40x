module cv32e40x_sequencer
import cv32e40x_pkg::*;
 (
    input  logic       clk,
    input  logic       rst_n,
    input  inst_resp_t instr_i,          // Instruction from prefetch unit
    input  logic       instr_is_ptr_i,   // Pointer flag, instr_i does not contain an instruction
    input  logic       valid_i,          // valid input from if stage
    input  logic       ready_i,          // Downstream is ready (ID stage)
    output inst_resp_t instr_o,          // Output sequenced (32-bit) instruction
    output logic       valid_o,          // Output is valid - input is valid AND we decode a valid seq instruction
    output logic       ready_o,          // Sequencer is ready for new inputs
    output logic       seq_last_o,       // Last operation is being output
    output logic       illegal_instr_o   // todo: remove
  );

  seq_i              instr_cnt_q;        // Count number of emitted uncompressed instructions
  pushpop_decode_s   decode;             // Struct holding metatdata for current decoded instruction
  seq_instr_e        seq_instr;          // Type of current decoded instruction

  logic [31:0]       instr;              // Instruction word from prefetcher
  logic [3:0]        rlist;              // rlist for push/pop*

  // Helper signals to indicate type of instruction
  logic              seq_load;
  logic              seq_store;
  logic              seq_move_a2s;
  logic              seq_move_s2a;

  // FSM state
  seq_state_e        seq_state_n;
  seq_state_e        seq_state_q;

  assign instr = instr_i.bus_resp.rdata;
  assign rlist = instr[7:4];

  // Control state (sequencer active or not), count
  // number of issued sub-instructions and set FSM state
  always_ff @( posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      instr_cnt_q <= '0;
      seq_state_q <= S_IDLE;
    end else begin
      if (valid_o && ready_i) begin
        if (!seq_last_o) begin
          instr_cnt_q <= instr_cnt_q + 1'd1;
        end else begin
          instr_cnt_q <= '0;
        end
      end else if (!valid_o) begin
        // Whenever we have no valid outputs, reset counter to 0.
        // This is factoring in kill_if and halt_if.
        instr_cnt_q <= '0;
      end

      seq_state_q <= seq_state_n;
    end
  end // always_ff

  ///////////////////////////////////
  // Decode sequenced instructions //
  ///////////////////////////////////
  // todo: detect all illegal encodings
  always_comb
  begin
    seq_instr    = INVALID_INST;
    illegal_instr_o = 1'b0; // todo: remove, and only set valid for actual valid instructions
    seq_load = 1'b0;
    seq_store = 1'b0;
    seq_move_a2s = 1'b0;
    seq_move_s2a = 1'b0;
    // All sequenced instructions are within C2
    if (instr[1:0] == 2'b10) begin
      if (instr[15:13] == 3'b101) begin
        unique case (instr[12:10])
          3'b011: begin
            if (instr[6:5] == 2'b11) begin
              // cm.mva01s
              seq_instr    = MVA01S;
              seq_move_s2a = 1'b1;
            end else if (instr[6:5] == 2'b01) begin
              // cm.mvsa01
              seq_instr    = MVSA01;
              seq_move_a2s = 1'b1;
            end
          end
          3'b110: begin
            if (instr[9:8] == 2'b00) begin
              // cm.push
              if (rlist > 3) begin
                seq_instr    = PUSH;
                seq_store = 1'b1;
              end else begin
                seq_instr = INVALID_INST;
                illegal_instr_o = 1'b1;
              end
            end else if (instr[9:8] == 2'b10) begin
              // cm.pop
              seq_instr    = POP;
              seq_load = 1'b1;
            end
          end
          3'b111: begin
            if (instr[9:8] == 2'b00) begin
              // cm.popretz
              seq_instr    = POPRETZ;
              seq_load = 1'b1;
            end else if (instr[9:8] == 2'b10) begin
              // cm.popret
              seq_instr    = POPRET;
              seq_load = 1'b1;
            end
          end
          default: begin
            seq_instr    = INVALID_INST;
          end
        endcase
      end // instr[15:13]
    end // C2
  end // always_comb

  // Local valid
  // In principle this is the same as "seq_en && valid_i"
  //   as the output of the above decode logic is equivalent to seq_en
  // todo: halting IF stage would imply !valid, can this be an issue?
  assign valid_o = (seq_instr != INVALID_INST) && !instr_is_ptr_i && valid_i;


  // Calculate number of S* registers needed in sequence (push/pop* only)
  assign decode.registers_saved = pushpop_reg_length(rlist);

  // Calculate stack space needed for the push/pop* registers (including ra)
  // 16-bit aligned
  assign decode.register_stack_adj = align_16(12'((decode.registers_saved+1'b1)<<2));


  // Compute extra stack adjustment from immediate bits
  // Immediate encodes number of extra 16 Byte blocks
  assign decode.additional_stack_adj = {6'd0,instr[3:2],4'd0};

  // Compute total stack adjustment based on saved registers and additional (from immediate)
  assign decode.total_stack_adj = decode.register_stack_adj + decode.additional_stack_adj;

  // Calculate the current stack address used for push/pop*
  always_comb begin : current_stack_adj
    case (seq_instr)
      PUSH: begin
        // Start pushing to -4(SP)
        decode.current_stack_adj = -{{instr_cnt_q+12'b1}<<2};
      end
      POP,POPRET, POPRETZ: begin
        // Need to account for any extra allocated stack space during cm.push
        // Rewind with decode.total_stack_adj and then start by popping from -4
        decode.current_stack_adj = decode.total_stack_adj-12'({instr_cnt_q+5'b1}<<2);
      end
      default:
        decode.current_stack_adj = '0;
    endcase
  end

  // Set current sreg number based on sequence counter
  assign decode.sreg = decode.registers_saved - instr_cnt_q - 4'd1;

  // Generate 32-bit instructions for all sequenced operations
  always_comb begin : sequencer_state_machine
    instr_o = instr_i;
    seq_state_n = seq_state_q;
    seq_last_o = 1'b0;

    ready_o = 1'b0;

    case (seq_state_q)
      S_IDLE: begin
        // First instruction is output here
        if (seq_load) begin
          instr_o.bus_resp.rdata = {decode.current_stack_adj,REG_SP,3'b010,sn_to_regnum(decode.sreg),OPCODE_LOAD};
        end else if (seq_store) begin
          instr_o.bus_resp.rdata = {decode.current_stack_adj[11:5],sn_to_regnum(decode.sreg),5'd2,3'b010,decode.current_stack_adj[4:0],OPCODE_STORE};
        end else if (seq_move_a2s) begin
          // addi s*, a0, 0
          instr_o.bus_resp.rdata = {12'h000, 5'd10, 3'b000, sn_to_regnum(5'(instr[9:7])), OPCODE_OPIMM};
        end else if (seq_move_s2a) begin
          // addi a0, s*, 0
          instr_o.bus_resp.rdata = {12'h000, sn_to_regnum(5'(instr[9:7])), 3'b000, 5'd10, OPCODE_OPIMM};
        end

        // Set next state when current instruction is accepted
        if (valid_o && ready_i) begin
          seq_state_n = (seq_move_a2s || seq_move_s2a) ? S_DMOVE :
                        seq_load                       ? S_POP   : S_PUSH;
        end

      end
      S_PUSH: begin
        instr_o.bus_resp.rdata = {decode.current_stack_adj[11:5],sn_to_regnum(decode.sreg),5'd2,3'b010,decode.current_stack_adj[4:0],OPCODE_STORE};
        // Advance FSM when we have saved all s* registers
        if (instr_cnt_q == decode.registers_saved) begin
          seq_state_n = S_RA;
        end
      end
      S_POP: begin
        instr_o.bus_resp.rdata = {decode.current_stack_adj,REG_SP,3'b010,sn_to_regnum(decode.sreg),OPCODE_LOAD};
        // Advance FSM when we have loaded all s* registers
        if (instr_cnt_q == decode.registers_saved) begin
          seq_state_n = S_RA;
        end
      end
      S_DMOVE: begin
        // Second half of double moves
        if (seq_move_a2s) begin
          // addi s*, a1, 0
          instr_o.bus_resp.rdata = {12'h000, 5'd11, 3'b000, sn_to_regnum(5'(instr[4:2])), OPCODE_OPIMM};
        end else if (seq_move_s2a) begin
          // addi a1, s*, 0
          instr_o.bus_resp.rdata = {12'h000, sn_to_regnum(5'(instr[4:2])), 3'b000, 5'd11, OPCODE_OPIMM};
        end
        if (ready_i) begin
          seq_state_n = S_IDLE;
          ready_o = 1'b1;
        end

        seq_last_o = 1'b1;
      end
      S_RA: begin
        // push pop ra register
        if (seq_load) begin
          instr_o.bus_resp.rdata = {decode.current_stack_adj,REG_SP,3'b010,REG_RA,OPCODE_LOAD};
        end else begin
          instr_o.bus_resp.rdata = {decode.current_stack_adj[11:5],5'd1,5'd2,3'b010,decode.current_stack_adj[4:0],OPCODE_STORE};
        end

        if (ready_i) begin
          seq_state_n = S_SP;
        end
      end
      S_SP: begin
        // Adjust stack pointer
        if (seq_load) begin
          instr_o.bus_resp.rdata = {decode.total_stack_adj,REG_SP,3'b0,REG_SP,OPCODE_OPIMM};
        end else begin
          instr_o.bus_resp.rdata = {-decode.total_stack_adj,5'd2,3'b0,5'd2,OPCODE_OPIMM};
        end

        if (ready_i) begin
          if (seq_instr == POPRETZ) begin
            seq_state_n = S_A0;
          end else if (seq_instr == POPRET) begin
            seq_state_n = S_RET;
          end else begin
            seq_state_n = S_IDLE;
            ready_o = 1'b1;
            seq_last_o = 1'b1;
          end
        end
      end
      S_A0: begin
        // Clear a0 for popretz
        instr_o.bus_resp.rdata = {12'h000,5'd0,3'b0,5'd10,OPCODE_OPIMM};

        if (ready_i) begin
          seq_state_n = S_RET;
        end
      end
      S_RET: begin
        // return for popret/popretz
        instr_o.bus_resp.rdata = {12'b0,REG_RA,3'b0,5'b0,OPCODE_JALR};

        if (ready_i) begin
          seq_state_n = S_IDLE;
          ready_o = 1'b1;
        end

        seq_last_o = 1'b1;
      end
    endcase

    // If there is no valid output, default to ready_o and IDLE state.
    // valid_i is already baked into valid_o and thus this takes effect on kill_if and halt_if
    if (!valid_o) begin
      ready_o = 1'b1;
      seq_state_n = S_IDLE;
    end
  end


endmodule