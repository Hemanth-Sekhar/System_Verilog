/* 
 * File Name      : 05_sva_enable_data_rule.sv
 * Date           : 08-Dec-2025
 * Description    : Immediate assertion example — when enable is high, data must be non-zero and even.
 * Copyright      : This SystemVerilog example is created for educational and project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic enable;
  logic [7:0] data;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Immediate assertion: data must be non-zero and even when enable is high
  always @(posedge clk) begin
    if (enable)
      assert ((data != 0) && (data % 2 == 0))
      else $error("SVA FAIL: data rule violated");
  end

  // Test stimulus
  initial begin
    enable = 0; data = 0;
    repeat (2) @(posedge clk);

    enable = 1; data = 8'd4;      // PASS — non-zero & even
    repeat (2) @(posedge clk);

    enable = 1; data = 8'd7;      // FAIL — odd
    repeat (2) @(posedge clk);

    enable = 1; data = 8'd0;      // FAIL — zero
    repeat (2) @(posedge clk);

    enable = 0; data = 8'd10;     // PASS — assertion not checked when enable = 0
    repeat (2) @(posedge clk);

    $finish;
  end

endm
