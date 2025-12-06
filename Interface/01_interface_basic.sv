// -----------------------------------------------------------------------------
// File Name   : 01_interface_basic.sv
// Date        : 06-12-2025
// Description : Demonstrates a basic SystemVerilog interface connecting a
//               testbench and DUT. The interface groups clk, reset, and data
//               signals. The testbench generates clock, drives reset and data
//               through the interface, and the DUT prints data on each posedge
//               of clk when reset is deasserted.
//               
//               This forms the foundation for later usage of modports and
//               virtual interfaces in UVM testbenches.
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

// DUT: prints data on posedge clk when reset == 0
module rtl (
  input  logic       clk,
  input  logic       reset,
  input  logic [7:0] data
);
  always @(posedge clk) begin
    if (!reset) begin
      $display("[%0t] Data = %0h", $time, data);
    end
  end
endmodule


// Interface grouping clk, reset, and data signals
interface intf();
  logic       clk;
  logic       reset;
  logic [7:0] data;
endinterface


// Testbench: drives interface and connects DUT
module tb();
  intf phy_intf();  // interface instance

  // Clock, reset, and stimulus
  initial begin
    phy_intf.clk   = 0;
    phy_intf.reset = 1;
    phy_intf.data  = '0;

    #20;                      // hold reset
    phy_intf.reset = 0;       // deassert reset

    forever #5 phy_intf.clk = ~phy_intf.clk;
  end

  // Stimulus for data
  initial begin
    #30 phy_intf.data = 8'hA5;
    #10 phy_intf.data = 8'h3C;
    #10 phy_intf.data = 8'hFF;
    #20 $finish;
  end

  // DUT connected to interface signals
  rtl dut (
    .clk   (phy_intf.clk),
    .reset (phy_intf.reset),
    .data  (phy_intf.data)
  );
endmodule
