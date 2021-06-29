


module alu_b_cpop
  (logic [31:0] operand_i,
   logic [ 5:0] result_o);

  logic [31:0][5:0] sum;

  assign result_o = sum[31];

  generate
    assign sum[0] = {5'h0, operand_i[0]};
    for (genvar i=1; i < 32; i++) begin
      assign sum[i] = sum[i-1] + {5'h0, operand_i[i]};
    end
  endgenerate

endmodule // alu_b_cpop
