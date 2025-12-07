/* 
 * File Name      : 02_sva_start_done_2cycle.sv
 * Date           : 07-12-2025
 * Description    : SVA delay implication example.
 *                  If 'start' is high in a cycle, 'done' must be high
 *                  exactly 2 clock cycles later. Demonstrates use of
 *                  '##' cycle delay in implication. Includes one PASS
 *                  and one FAIL scenario in stimulus for observation.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic start;
  logic done;

  // clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // stimulus
  initial begin
    start = 0;
    done  = 0;

    // PASS: done after 2 cycles
    @(posedge clk) start = 1;
    @(posedge clk) start = 0;
    @(posedge clk);          // 1st cycle after start
    @(posedge clk) done = 1; // 2nd cycle after start (OK)
    @(posedge clk) done = 0;

    // FAIL: done after 3 cycles
    @(posedge clk) start = 1;
    @(posedge clk) start = 0;
    @(posedge clk);          // 1st
    @(posedge clk);          // 2nd (should be done here)
    @(posedge clk) done = 1; // too late → FAIL
    @(posedge clk) done = 0;

    #30 $finish;
  end

  // SVA: start must be followed by done exactly 2 cycles later
  property check;
    @(posedge clk) start |-> ##2 done;
  endproperty

  assert property (check)
    else $error("DONE is not high exactly 2 cycles after START");

endmodule
