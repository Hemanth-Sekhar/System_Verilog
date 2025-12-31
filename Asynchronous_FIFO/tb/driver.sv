class driver;
  packet pkt;
  virtual intf vif;

  // Entry task
  task run();
    // Bind interface once
    vif = common::vif;
    if (vif == null)
      $fatal("DRIVER: virtual interface not bound");

    // Default values
    vif.w_en    = 0;
    vif.r_en    = 0;
    vif.data_in = '0;

    // Wait for resets to deassert
    wait (vif.wrst_n == 1);
    wait (vif.rrst_n == 1);

    // Spawn independent clock-domain processes
    fork
      write_process();
      read_process();
    join_none
  endtask


  // ================= WRITE DOMAIN =================
  task write_process();
    forever begin
      @(posedge vif.wclk);

      // default
      vif.w_en = 0;

      // write only if FIFO not full
      if (!vif.full) begin
        $display("DRIVER: waiting for packet...");
        common::gen2dri.get(pkt);   // block until packet available
        pkt.print("DRIVER");
        vif.w_en    <= 1;
        vif.data_in <= pkt.data_in;
      end
    end
  endtask


  // ================= READ DOMAIN =================
  task read_process();
    forever begin
      @(posedge vif.rclk);

      // default
      vif.r_en = 0;

      // read only if FIFO not empty
      if (!vif.empty) begin
        vif.r_en <= 1;
        pkt.print("DRIVER");
      end
    end
  endtask

endclass

