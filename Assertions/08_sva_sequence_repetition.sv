/* 
 * File Name      : 08_sva_sequence_repetition.sv
 * Date           : 08-Dec-2025
 * Description    : SVA sequence repetition examples:
 *                  1) write_req must remain high for at least 2 cycles
 *                  2) burst_active must be high for exactly 4 cycles after burst_start
 * Copyright      : This SystemVerilog example is created for educational and project 
 *                  documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this file 
 *                  with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic write_req;
  logic burst_start, burst_active;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //========================================================
  // SVA: Sequence repetition
  //========================================================

  // 1) write_req must stay high for at least 2 consecutive cycles
  sequence s_write_req_min2;
    write_req[*2:$];
  endsequence

  property p_write_req_min2;
    @(posedge clk) s_write_req_min2;
  endproperty

  assert property (p_write_req_min2)
    else $error("write_req not held high for at least 2 cycles");

  // 2) burst_active must be high for exactly 4 cycles after burst_start
  sequence s_burst_active_4;
    burst_start ##1 burst_active[*4];
  endsequence

  property p_burst_active_4;
    @(posedge clk) s_burst_active_4;
  endproperty

  assert property (p_burst_active_4)
    else $error("burst_active not high for exactly 4 cycles after burst_start");

  //========================================================
  // Stimulus: create PASS and FAIL scenarios
  //========================================================

  initial begin
    write_req    = 0;
    burst_start  = 0;
    burst_active = 0;

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // PASS: write_req high for 3 cycles (>=2)
    // --------------------------------------------
    @(posedge clk);
    write_req <= 1;           // cycle 0
    @(posedge clk);
    write_req <= 1;           // cycle 1
    @(posedge clk);
    write_req <= 1;           // cycle 2
    @(posedge clk);
    write_req <= 0;

    // --------------------------------------------
    // FAIL: write_req high for only 1 cycle
    // --------------------------------------------
    repeat (2) @(posedge clk);
    @(posedge clk);
    write_req <= 1;           // only this cycle high
    @(posedge clk);
    write_req <= 0;           // drops too early → FAIL

    // --------------------------------------------
    // PASS: burst_active high for exactly 4 cycles
    // --------------------------------------------
    repeat (3) @(posedge clk);
    @(posedge clk);
    burst_start  <= 1;
    @(posedge clk);
    burst_start  <= 0;
    burst_active <= 1;        // 1st cycle after start
    @(posedge clk);
    burst_active <= 1;        // 2nd
    @(posedge clk);
    burst_active <= 1;        // 3rd
    @(posedge clk);
    burst_active <= 1;        // 4th
    @(posedge clk);
    burst_active <= 0;        // done → PASS

    // --------------------------------------------
    // FAIL: burst_active only 3 cycles high
    // --------------------------------------------
    repeat (3) @(posedge clk);
    @(posedge clk);
    burst_start  <= 1;
    @(posedge clk);
    burst_start  <= 0;
    burst_active <= 1;        // 1st
    @(posedge clk);
    burst_active <= 1;        // 2nd
    @(posedge clk);
    burst_active <= 1;        // 3rd
    @(posedge clk);
    burst_active <= 0;        // ends too early → FAIL

    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
