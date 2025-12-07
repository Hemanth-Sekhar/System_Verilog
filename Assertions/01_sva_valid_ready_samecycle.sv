/* 
 * File Name      : 01_sva_valid_ready_samecycle.sv
 * Date           : 07-12-2025
 * Description    : Basic SVA implication example
 *                  If 'valid' is high in a cycle, 'ready' must be high
 *                  in the same cycle. Assertion triggers on posedge clk.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;
  logic clk, valid, ready;

  // clock
  initial begin
    clk  = 0;
    forever #5 clk = ~clk;
  end

  // stimulus
  initial begin
    valid = 0; ready = 0;

    @(posedge clk) valid = 0; ready = 0;
    @(posedge clk) valid = 0; ready = 1;
    @(posedge clk) valid = 1; ready = 0;  // FAIL
    @(posedge clk) valid = 1; ready = 1;  // PASS
    @(posedge clk) valid = 0; ready = 0;  // NO CHECK
    @(posedge clk) valid = 0; ready = 1;  // NO CHECK
    @(posedge clk) valid = 1; ready = 0;  // FAIL

    #20 $finish;
  end

  // SVA: if valid is high, ready must be high in same cycle
  property check;
    @(posedge clk) valid |-> ready;
  endproperty

  assert property (check)
    else $error("READY is NOT high in same cycle as VALID");

endmodule
