class monitor;
  virtual intf vif;

  // Entry point
  task run();
    vif = common::vif;
    if (vif == null)
      $fatal("MONITOR: virtual interface not bound");

    // Spawn independent sampling processes
    fork
      monitor_write();
      monitor_read();
    join_none
  endtask


  // ================= WRITE MONITOR =================
  task monitor_write();
    packet pkt;
    forever begin
      @(posedge vif.wclk);

      if (vif.w_en && !vif.full) begin
        pkt = new();
        pkt.w_en     = vif.w_en;
        pkt.data_in  = vif.data_in;
        pkt.full     = vif.full;
        pkt.empty    = vif.empty;

        pkt.print("MONITOR_WRITE");
        common::mon2scb.put(pkt);
      end
    end
  endtask


  // ================= READ MONITOR =================
  task monitor_read();
    packet pkt;
    forever begin
      @(posedge vif.rclk);

      if (vif.r_en && !vif.empty) begin
        pkt = new();
        pkt.r_en      = vif.r_en;
        pkt.data_out  = vif.data_out;
        pkt.full      = vif.full;
        pkt.empty     = vif.empty;

        pkt.print("MONITOR_READ");
        common::mon2scb.put(pkt);
      end
    end
  endtask

endclass

