/* 
 * File Name      : 04_sva_wrreq_wrack_nextcycle.sv
 * Date           : 07-12-2025
 * Description    : Demonstrates non-overlapped implication (|=>).
 *                  If 'wr_req' is high in a cycle, 'wr_ack' must be high
 *                  in the next cycle. Includes one PASS and one FAIL
 *                  scenario to illustrate assertion behavior in simulation.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk, wr_req, wr_ack;

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    wr_req = 0; wr_ack = 0;

    @(posedge clk) wr_req = 1; wr_ack = 0;   // request
    @(posedge clk) wr_req = 0; wr_ack = 1;   // acknowledge (PASS)
    @(posedge clk) wr_req = 1; wr_ack = 0;   // request
    @(posedge clk) wr_req = 0; wr_ack = 0;   // missing ack (FAIL)

    #30 $finish;
  end

  // SVA: wr_ack must be high in the NEXT cycle when wr_req is high
  property check;
    @(posedge clk) wr_req |=> wr_ack;
  endproperty

  assert property (check)
    else $error("ERROR: wr_ack not high in next cycle after wr_req");

endmodule
