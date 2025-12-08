/* 
 * File Name      : 07_sva_delay.sv
 * Date           : 08-Dec-2025
 * Description    : Concurrent assertions using sequence delays (## and ##[m:n]).
 *                  1) write_req -> write_ack exactly 3 cycles later
 *                  2) rd_req -> rd_data_valid within 2 to 4 cycles
 * Copyright      : This SystemVerilog example is created for educational and project 
 *                  documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this file 
 *                  with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic write_req, write_ack;
  logic rd_req, rd_data_valid;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //====================================================================
  // SVA: Sequence-based delay checks
  //====================================================================

  // 1) write_req -> write_ack exactly 3 cycles later
  sequence s_write_ack_3;
    write_req ##3 write_ack;
  endsequence

  property p_write_ack_3;
    @(posedge clk) s_write_ack_3;
  endproperty

  assert property (p_write_ack_3)
    else $error("write_ack not asserted exactly 3 cycles after write_req");

  // 2) rd_req -> rd_data_valid within 2 to 4 cycles
  sequence s_rd_valid_2_4;
    rd_req ##[2:4] rd_data_valid;
  endsequence

  property p_rd_valid_2_4;
    @(posedge clk) s_rd_valid_2_4;
  endproperty

  assert property (p_rd_valid_2_4)
    else $error("rd_data_valid not asserted within 2-4 cycles after rd_req");

  //====================================================================
  // Stimulus – create pass and fail scenarios
  //====================================================================

  initial begin
    write_req = 0; write_ack = 0;
    rd_req = 0;   rd_data_valid = 0;

    repeat (2) @(posedge clk);

    // ------------------------------------------------------------
    // PASS case for write_req / write_ack (ack at +3 cycles)
    // ------------------------------------------------------------
    @(posedge clk);
    write_req <= 1;
    @(posedge clk);
    write_req <= 0;      // req pulse done

    // +1 cycle
    @(posedge clk);
    write_ack <= 0;
    // +2 cycle
    @(posedge clk);
    write_ack <= 0;
    // +3 cycle → ack asserted here → PASS
    @(posedge clk);
    write_ack <= 1;
    @(posedge clk);
    write_ack <= 0;

    // ------------------------------------------------------------
    // FAIL case for write_req / write_ack (ack at wrong time)
    // ------------------------------------------------------------
    @(posedge clk);
    write_req <= 1;
    @(posedge clk);
    write_req <= 0;

    // Wrong ack timing (e.g., at +2 instead of +3)
    @(posedge clk);
    write_ack <= 0;
    @(posedge clk);
    write_ack <= 1;   // +2 cycle (FAIL for p_write_ack_3)
    @(posedge clk);
    write_ack <= 0;

    // ------------------------------------------------------------
    // PASS case for rd_req / rd_data_valid (within 2–4 cycles)
    // ------------------------------------------------------------
    @(posedge clk);
    rd_req <= 1;
    @(posedge clk);
    rd_req <= 0;

    // data_valid at +2 cycles → PASS
    @(posedge clk);
    rd_data_valid <= 0;
    @(posedge clk);
    rd_data_valid <= 1;
    @(posedge clk);
    rd_data_valid <= 0;

    // ------------------------------------------------------------
    // FAIL case for rd_req / rd_data_valid (after 4 cycles)
    // ------------------------------------------------------------
    @(posedge clk);
    rd_req <= 1;
    @(posedge clk);
    rd_req <= 0;

    // Now assert data_valid too late (e.g., +5 cycles)
    @(posedge clk); // +1
    rd_data_valid <= 0;
    @(posedge clk); // +2
    rd_data_valid <= 0;
    @(posedge clk); // +3
    rd_data_valid <= 0;
    @(posedge clk); // +4
    rd_data_valid <= 0;
    @(posedge clk); // +5 → too late → FAIL
    rd_data_valid <= 1;
    @(posedge clk);
    rd_data_valid <= 0;

    repeat (3) @(posedge clk);
    $finish;
  end

endmodule
