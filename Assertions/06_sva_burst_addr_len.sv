/* 
 * File Name      : 06_sva_burst_addr_len.sv
 * Date           : 08-Dec-2025
 * Description    : Concurrent assertions for burst start handshake.
 *                  1) burst_len must remain same in the next cycle after burst_start
 *                  2) addr must increment by 4 in the next cycle after burst_start
 * Copyright      : This SystemVerilog example is created for educational and project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic burst_start;
  logic [7:0] burst_len;
  logic [31:0] addr;

  // Clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Property 1: burst_len must remain unchanged on the next cycle after burst_start
  property p_len_stable;
    @(posedge clk) burst_start |=> (burst_len == $past(burst_len));
  endproperty
  assert property (p_len_stable)
    else $error("burst_len changed unexpectedly after burst_start");

  // Property 2: addr must increment by 4 on the next cycle after burst_start
  property p_addr_inc;
    @(posedge clk) burst_start |=> (addr == $past(addr) + 4);
  endproperty
  assert property (p_addr_inc)
    else $error("addr failed to increment by 4 after burst_start");

  // Stimulus – includes pass and fail cases
  initial begin
    burst_start = 0; burst_len = 8'd4; addr = 32'h0000_1000;
    repeat (2) @(posedge clk);

    burst_start = 1; burst_len = 8'd4; addr = 32'h0000_1000;   // PASS — len same, addr +4
    @(posedge clk);
                       burst_len = 8'd4; addr = 32'h0000_1004;
    @(posedge clk);

    burst_start = 1; burst_len = 8'd5; addr = 32'h0000_2000;   // FAIL — len changed
    @(posedge clk);
                       burst_len = 8'd6; addr = 32'h0000_2004;
    @(posedge clk);

    burst_start = 1; burst_len = 8'd4; addr = 32'h0000_3000;   // FAIL — addr not +4
    @(posedge clk);
                       burst_len = 8'd4; addr = 32'h0000_3008;
    @(posedge clk);

    $finish;
  end

endmodule
