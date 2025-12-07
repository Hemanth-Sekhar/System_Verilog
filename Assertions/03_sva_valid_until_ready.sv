/* 
 * File Name      : 03_sva_valid_until_ready.sv
 * Date           : 07-12-2025
 * Description    : SVA for streaming-style valid/ready rule.
 *                  When 'valid' rises, it must remain high until
 *                  'ready' becomes high. If 'valid' drops before
 *                  'ready', assertion fails. Includes one PASS and
 *                  one FAIL scenario for observation in simulation.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic valid;
  logic ready;

  // clock
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // stimulus
  initial begin
    valid = 0;
    ready = 0;

    // PASS case: valid stays high until ready
    @(posedge clk) valid = 1; ready = 0;
    @(posedge clk) valid = 1; ready = 0;
    @(posedge clk) valid = 1; ready = 1;   // ready goes high -> allowed to drop
    @(posedge clk) valid = 0; ready = 0;

    // FAIL case: valid drops before ready
    @(posedge clk) valid = 1; ready = 0;   // rise: start check
    @(posedge clk) valid = 0; ready = 0;   // violation: valid dropped early
    @(posedge clk) valid = 0; ready = 1;

    #40 $finish;
  end

  // SVA: when valid rises, it must stay high until ready
  property check;
    @(posedge clk) $rose(valid) |-> (valid until ready);
  endproperty

  assert property (check)
    else $error("ERROR: valid dropped before ready went high");

endmodule
