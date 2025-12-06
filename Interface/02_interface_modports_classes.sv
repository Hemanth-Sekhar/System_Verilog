// -----------------------------------------------------------------------------
// File Name   : 02_interface_modports_classes.sv
// Date        : 06-12-2025
// Description : Demonstrates SystemVerilog interface with modports and usage
//               inside class-based driver and monitor using virtual interfaces.
//               The driver drives 'data' through driver_mp, the monitor observes
//               'data' through monitor_mp, and the DUT prints data on each
//               posedge of clk when reset is deasserted.
//               
//               This is a stepping stone towards UVM-style driver/monitor
//               connected to the DUT via virtual interfaces and modports.
//               
// Copyright (c) 2025 Hemanth Sekhar
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this HDL source file to use, copy, modify, merge, publish, or distribute
// it for educational or non-commercial purposes, provided that this notice is
// included in all copies or substantial portions of the file.
//
// THIS HDL SOURCE FILE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// FUNCTIONAL CORRECTNESS, PERFORMANCE, OR FITNESS FOR A PARTICULAR PURPOSE.
//
// Author      : Hemanth Sekhar
// Email       : khsekhar9@gmail.com
// -----------------------------------------------------------------------------

// Simple DUT: prints data on posedge clk when reset == 0
module rtl (
  input  logic       clk,
  input  logic       reset,
  input  logic [7:0] data
);
  always @(posedge clk) begin
    if (!reset) begin
      $display("[%0t] DUT : Data = %0h", $time, data);
    end
  end
endmodule


// Interface with modports for driver and monitor views
interface intf();
  logic       clk;
  logic       reset;
  logic [7:0] data;

  // Driver can drive data, monitor can only read
  modport driver_mp  (input clk, input reset, output data);
  modport monitor_mp (input clk, input reset, input  data);
endinterface


// Class-based driver using virtual interface with driver modport
class driver;
  virtual intf.driver_mp vif;

  function new(virtual intf.driver_mp vif);
    this.vif = vif;
  endfunction

  task run();
    $display("[%0t] DRIVER: starting", $time);

    // Wait until reset is deasserted
    @(negedge vif.reset);

    // Drive data on a few clock cycles
    @(posedge vif.clk);
    vif.data = 8'h15;

    @(posedge vif.clk);
    vif.data = 8'h29;

    @(posedge vif.clk);
    vif.data = 8'hA5;

    $display("[%0t] DRIVER: finished driving", $time);
  endtask
endclass


// Class-based monitor using virtual interface with monitor modport
class monitor;
  virtual intf.monitor_mp vif;

  function new(virtual intf.monitor_mp vif);
    this.vif = vif;
  endfunction

  task run();
    $display("[%0t] MONITOR: starting", $time);
    forever begin
      @(posedge vif.clk);
      if (!vif.reset)
        $display("[%0t] MON  : Observed data = %0h", $time, vif.data);
    end
  endtask
endclass


// Testbench: creates interface, DUT, driver, and monitor
module tb;
  intf    phy_intf();   // Interface instance
  driver  dri;
  monitor mon;

  // Clock and reset generation
  initial begin
    phy_intf.clk   = 0;
    phy_intf.reset = 1;
    phy_intf.data  = '0;

    // Apply reset for some time
    #20;
    phy_intf.reset = 0;

    // Free-running clock
    forever #5 phy_intf.clk = ~phy_intf.clk;
  end

  // Create driver/monitor and start their run() tasks
  initial begin
    dri = new(phy_intf); // binds to driver_mp view
    mon = new(phy_intf); // binds to monitor_mp view

    fork
      dri.run();
      mon.run();
    join_none

    // Stop simulation after some time
    #200;
    $finish;
  end

  // DUT connected to full interface signals (not via modport)
  rtl dut (
    .clk   (phy_intf.clk),
    .reset (phy_intf.reset),
    .data  (phy_intf.data)
  );
endmodule
