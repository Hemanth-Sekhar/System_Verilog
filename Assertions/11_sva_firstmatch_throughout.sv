/* 
 * File Name      : 11_sva_firstmatch_throughout.sv
 * Date           : 08-Dec-2025
 * Description    : SVA examples using local variables, first_match, and throughout
 *                  1) cmd -> first done within 1–6 cycles with data check
 *                  2) transfer_start -> transfer_active must remain high throughout beat_valid window
 * Copyright      : This SystemVerilog example is created for educational and 
 *                  project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this 
 *                  file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic cmd, done;
  logic [7:0] data_prev, data_next;

  logic transfer_start;
  logic transfer_active;
  logic beat_valid;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //========================================================
  // SVA: first_match + local variable
  //========================================================

  // Requirement:
  // When cmd is high, find the FIRST done within 1–6 cycles,
  // and check data_next == data_prev + 8 at that moment.
  property p1;
    logic [7:0] temp;
    @(posedge clk)
      first_match(
        (cmd, temp = data_prev) ##[1:6] (done && (data_next == temp + 8))
      );
  endproperty

  assert property (p1)
    else $error("data_next != data_prev + 8 at first done within 1-6 cycles of cmd");

  //========================================================
  // SVA: throughout
  //========================================================

  // Requirement:
  // After transfer_start, transfer_active must remain high
  // throughout the period where beat_valid is high.
  property p2;
    @(posedge clk)
      transfer_start |-> (transfer_active throughout beat_valid[*1:$]);
  endproperty

  assert property (p2)
    else $error("transfer_active dropped while beat_valid was high after transfer_start");

  //========================================================
  // Stimulus: PASS and FAIL scenarios
  //========================================================

  initial begin
    cmd = 0; done = 0;
    data_prev = 0; data_next = 0;

    transfer_start = 0;
    transfer_active = 0;
    beat_valid = 0;

    repeat (3) @(posedge clk);

    //------------------------------
    // PASS case for p1
    //------------------------------
    cmd <= 1;
    data_prev <= 8'd20;
    @(posedge clk);
    cmd <= 0;

    // First done at +2 cycles → check data_next = temp + 8 = 28
    @(posedge clk);
    done <= 1; data_next <= 8'd28;     // PASS
    @(posedge clk);
    done <= 0;

    repeat (3) @(posedge clk);

    //------------------------------
    // FAIL case for p1
    //------------------------------
    cmd <= 1;
    data_prev <= 8'd15;
    @(posedge clk);
    cmd <= 0;

    // done occurs within window but wrong data_next
    @(posedge clk);
    done <= 1; data_next <= 8'd30;     // expected 15 + 8 = 23 → FAIL
    @(posedge clk);
    done <= 0;

    repeat (4) @(posedge clk);

    //------------------------------
    // PASS case for p2
    //------------------------------
    transfer_start <= 1;
    transfer_active <= 1;
    beat_valid <= 1;
    @(posedge clk);
    transfer_start <= 0;

    // beat_valid active window → transfer_active stays high
    beat_valid <= 1;
    @(posedge clk);
    beat_valid <= 1;
    @(posedge clk);
    beat_valid <= 0;
    transfer_active <= 0;   // allowed after window closes

    repeat (3) @(posedge clk);

    //------------------------------
    // FAIL case for p2
    //------------------------------
    transfer_start <= 1;
    transfer_active <= 1;
    beat_valid <= 1;
    @(posedge clk);
    transfer_start <= 0;

    // transfer_active drops while beat_valid still high → FAIL
    transfer_active <= 0;
    beat_valid <= 1;
    @(posedge clk);
    beat_valid <= 0;

    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
