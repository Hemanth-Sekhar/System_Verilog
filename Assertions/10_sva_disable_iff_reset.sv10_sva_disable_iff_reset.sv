/* 
 * File Name      : 10_sva_disable_iff_reset.sv
 * Date           : 08-Dec-2025
 * Description    : Reset-safe SVA examples using disable iff:
 *                  1) Counter increments by 1 when cnt_en is high (next cycle)
 *                  2) FIFO write must not occur when fifo_full is high
 * Copyright      : This SystemVerilog example is created for educational and 
 *                  project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this 
 *                  file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic        clk;
  logic        rst_n;
  logic        cnt_en;
  logic [7:0]  cnt;
  logic        wr_en;
  logic        fifo_full;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Reset generation (active-low)
  initial begin
    rst_n = 0;
    cnt_en = 0;
    cnt = 0;
    wr_en = 0;
    fifo_full = 0;

    repeat (3) @(posedge clk);
    rst_n = 1;   // deassert reset
  end

  // Simple counter model for demonstration
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cnt <= '0;
    end else begin
      if (cnt_en)
        cnt <= cnt + 1;
    end
  end

  //========================================================
  // SVA: reset-safe properties using disable iff
  //========================================================

  // 1) Counter increment rule: when cnt_en is high,
  //    cnt must increment by 1 in the next cycle (ignore reset)
  property p_cnt_inc;
    @(posedge clk) disable iff (!rst_n)
      cnt_en |=> (cnt == $past(cnt) + 1);
  endproperty

  assert property (p_cnt_inc)
    else $error("cnt did not increment by 1 when cnt_en is high");

  // 2) FIFO write rule: when wr_en is high,
  //    fifo_full must not be high in the same cycle (ignore reset)
  property p_fifo_write_safe;
    @(posedge clk) disable iff (!rst_n)
      wr_en |-> !fifo_full;
  endproperty

  assert property (p_fifo_write_safe)
    else $error("write attempted when fifo_full is high");

  //========================================================
  // Stimulus: PASS and FAIL scenarios
  //========================================================

  initial begin
    // Wait for reset deassert
    @(posedge rst_n);
    repeat (2) @(posedge clk);

    // --------------------------------------------
    // PASS: cnt_en with proper increment
    // --------------------------------------------
    $display("PASS case for counter increment");
    cnt_en <= 1;
    @(posedge clk);   // cnt should increment by +1
    @(posedge clk);
    cnt_en <= 0;

    repeat (2) @(posedge clk);

    // --------------------------------------------
    // FAIL: cnt_en high but cnt does not increment
    // (we intentionally block increment using manual override)
    // --------------------------------------------
    $display("FAIL case for counter increment");
    cnt_en <= 1;
    @(posedge clk);
    // Freeze cnt to create failure (model bug)
    cnt <= cnt;  // in real bug, design wouldn't increment
    @(posedge clk);
    cnt_en <= 0;

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // PASS: wr_en while fifo_full == 0
    // --------------------------------------------
    $display("PASS case for FIFO write");
    wr_en     <= 1;
    fifo_full <= 0;   // legal write
    @(posedge clk);
    wr_en     <= 0;

    repeat (2) @(posedge clk);

    // --------------------------------------------
    // FAIL: wr_en while fifo_full == 1
    // --------------------------------------------
    $display("FAIL case for FIFO write");
    fifo_full <= 1;
    wr_en     <= 1;   // illegal write → assertion should fire
    @(posedge clk);
    wr_en     <= 0;
    fifo_full <= 0;

    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
