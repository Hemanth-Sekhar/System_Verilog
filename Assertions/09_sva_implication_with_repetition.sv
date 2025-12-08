/* 
 * File Name      : 09_sva_implication_with_repetition.sv
 * Date           : 08-Dec-2025
 * Description    : SVA examples using implication with repetition:
 *                  1) Overlapped: tx_start |-> tx_active[*4]
 *                  2) Non-overlapped: rx_start |=> rx_valid[*3]
 * Copyright      : This SystemVerilog example is created for educational and 
 *                  project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this 
 *                  file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;
  logic tx_start, tx_active;
  logic rx_start, rx_valid;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //========================================================
  // SVA: implication with repetition
  //========================================================

  // 1) Overlapped: tx_start -> tx_active high for 4 cycles
  property p_tx_active_4;
    @(posedge clk) tx_start |-> tx_active[*4];
  endproperty

  assert property (p_tx_active_4)
    else $error("tx_active not high for 4 cycles starting same cycle as tx_start");

  // 2) Non-overlapped: rx_start -> rx_valid high for 3 cycles from next cycle
  property p_rx_valid_3;
    @(posedge clk) rx_start |=> rx_valid[*3];
  endproperty

  assert property (p_rx_valid_3)
    else $error("rx_valid not high for 3 cycles starting next cycle after rx_start");

  //========================================================
  // Stimulus: PASS and FAIL cases
  //========================================================

  initial begin
    tx_start  = 0;
    tx_active = 0;
    rx_start  = 0;
    rx_valid  = 0;

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // PASS: tx_start + tx_active high for 4 cycles
    // --------------------------------------------
    @(posedge clk);
    tx_start  <= 1;
    tx_active <= 1;   // cycle 0 (start cycle)
    @(posedge clk);
    tx_start  <= 0;
    tx_active <= 1;   // cycle 1
    @(posedge clk);
    tx_active <= 1;   // cycle 2
    @(posedge clk);
    tx_active <= 1;   // cycle 3
    @(posedge clk);
    tx_active <= 0;   // done → PASS

    // --------------------------------------------
    // FAIL: tx_active only 3 cycles instead of 4
    // --------------------------------------------
    repeat (3) @(posedge clk);
    @(posedge clk);
    tx_start  <= 1;
    tx_active <= 1;   // cycle 0
    @(posedge clk);
    tx_start  <= 0;
    tx_active <= 1;   // cycle 1
    @(posedge clk);
    tx_active <= 1;   // cycle 2
    @(posedge clk);
    tx_active <= 0;   // should be 1 more cycle → FAIL

    // --------------------------------------------
    // PASS: rx_start + rx_valid high for 3 cycles (from next)
    // --------------------------------------------
    repeat (4) @(posedge clk);
    @(posedge clk);
    rx_start <= 1;
    @(posedge clk);        // next cycle after start
    rx_start <= 0;
    rx_valid <= 1;         // cycle 1
    @(posedge clk);
    rx_valid <= 1;         // cycle 2
    @(posedge clk);
    rx_valid <= 1;         // cycle 3
    @(posedge clk);
    rx_valid <= 0;         // done → PASS

    // --------------------------------------------
    // FAIL: rx_valid only 2 cycles instead of 3
    // --------------------------------------------
    repeat (4) @(posedge clk);
    @(posedge clk);
    rx_start <= 1;
    @(posedge clk);        // next cycle
    rx_start <= 0;
    rx_valid <= 1;         // cycle 1
    @(posedge clk);
    rx_valid <= 1;         // cycle 2
    @(posedge clk);
    rx_valid <= 0;         // too early → FAIL

    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
