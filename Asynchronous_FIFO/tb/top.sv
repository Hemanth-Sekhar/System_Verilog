module top;

  // Interface
  intf phy_intf();

  // Test
  test t0();

  // Bind interface globally
  initial begin
    common::vif = phy_intf;
  end

  // WRITE CLOCK
  initial begin
    phy_intf.wclk = 0;
    forever #10 phy_intf.wclk = ~phy_intf.wclk;
  end

  // READ CLOCK
  initial begin
    phy_intf.rclk = 0;
    forever #15 phy_intf.rclk = ~phy_intf.rclk;
  end

  // RESET (ACTIVE LOW)
  initial begin
    phy_intf.wrst_n = 0;
    phy_intf.rrst_n = 0;
    #50;
    phy_intf.wrst_n = 1;
    phy_intf.rrst_n = 1;
  end

  // DUT
  asynchronous_fifo dut (
    .wclk     (phy_intf.wclk),
    .rclk     (phy_intf.rclk),
    .wrst_n   (phy_intf.wrst_n),
    .rrst_n   (phy_intf.rrst_n),
    .w_en     (phy_intf.w_en),
    .r_en     (phy_intf.r_en),
    .data_in  (phy_intf.data_in),
    .data_out (phy_intf.data_out),
    .full     (phy_intf.full),
    .empty    (phy_intf.empty)
  );

endmodule
