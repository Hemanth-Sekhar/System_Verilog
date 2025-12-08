/* 
 * File Name      : 12_sva_within_frame_transfer.sv
 * Date           : 08-Dec-2025
 * Description    : SVA examples using 'within':
 *                  1) header_valid ##1 payload_valid must occur within frame window
 *                  2) transfer_done must occur within transfer window
 * Copyright      : This SystemVerilog example is created for educational and 
 *                  project documentation purposes.
 * Permission     : Permission is granted to use, modify, and distribute this 
 *                  file with author attribution.
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

module tb;

  logic clk;

  // Frame-related signals
  logic frame_start;
  logic frame_active;
  logic header_valid;
  logic payload_valid;

  // Transfer-related signals
  logic transfer_start;
  logic transfer_active;
  logic transfer_done;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  //========================================================
  // SVA: 'within' – frame header/payload inside frame window
  //========================================================

  // Frame window: frame_start, then frame_active high for 1+ cycles
  sequence s_frame_window;
    frame_start ##1 frame_active[*1:$];
  endsequence

  // Header/payload pattern: header_valid then payload_valid next cycle
  sequence s_header_payload;
    header_valid ##1 payload_valid;
  endsequence

  property p_header_payload_within_frame;
    @(posedge clk)
      s_header_payload within s_frame_window;
  endproperty

  assert property (p_header_payload_within_frame)
    else $error("header_valid -> payload_valid did not occur within frame window");

  //========================================================
  // SVA: 'within' – transfer_done inside transfer window
  //========================================================

  // Transfer window: transfer_start, then transfer_active high for 1+ cycles
  sequence s_transfer_window;
    transfer_start ##1 transfer_active[*1:$];
  endsequence

  // transfer_done event (single pulse)
  sequence s_transfer_done_evt;
    transfer_done;
  endsequence

  property p_transfer_done_within_window;
    @(posedge clk)
      s_transfer_done_evt within s_transfer_window;
  endproperty

  assert property (p_transfer_done_within_window)
    else $error("transfer_done did not occur within transfer window");

  //========================================================
  // Stimulus: PASS and FAIL scenarios
  //========================================================

  initial begin
    frame_start      = 0;
    frame_active     = 0;
    header_valid     = 0;
    payload_valid    = 0;

    transfer_start   = 0;
    transfer_active  = 0;
    transfer_done    = 0;

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // PASS: header/payload inside frame window
    // --------------------------------------------
    // Frame window open
    frame_start  <= 1;
    @(posedge clk);
    frame_start  <= 0;
    frame_active <= 1;   // frame window begins
    // header/payload pattern fully inside frame_active region
    @(posedge clk);
    header_valid  <= 1;
    @(posedge clk);
    header_valid  <= 0;
    payload_valid <= 1;
    @(posedge clk);
    payload_valid <= 0;
    frame_active  <= 0;  // frame window closes

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // FAIL: header/payload outside frame window
    // (pattern occurs when no frame window is active)
    // --------------------------------------------
    header_valid  <= 1;
    @(posedge clk);
    header_valid  <= 0;
    payload_valid <= 1;
    @(posedge clk);
    payload_valid <= 0;

    repeat (4) @(posedge clk);

    // --------------------------------------------
    // PASS: transfer_done inside transfer window
    // --------------------------------------------
    transfer_start  <= 1;
    @(posedge clk);
    transfer_start  <= 0;
    transfer_active <= 1;   // transfer window begins
    @(posedge clk);
    transfer_done   <= 1;   // event inside window → PASS
    @(posedge clk);
    transfer_done   <= 0;
    @(posedge clk);
    transfer_active <= 0;   // window closes

    repeat (3) @(posedge clk);

    // --------------------------------------------
    // FAIL: transfer_done outside transfer window
    // (event happens after window ends)
    // --------------------------------------------
    transfer_start  <= 1;
    @(posedge clk);
    transfer_start  <= 0;
    transfer_active <= 1;
    @(posedge clk);
    transfer_active <= 0;   // window closed
    @(posedge clk);
    transfer_done   <= 1;   // too late → FAIL
    @(posedge clk);
    transfer_done   <= 0;

    repeat (5) @(posedge clk);
    $finish;
  end

endmodule
