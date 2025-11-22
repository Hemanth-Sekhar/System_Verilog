// -----------------------------------------------------------------------------
// File Name   : 01_data_types_def_values.sv
// Date        : 22-11-2025
// Description : Displays the default values of basic SystemVerilog data types
//               including reg, wire, integer, real, time, realtime, bit, byte,
//               logic, shortint, int, longint, and shortreal. This serves as a
//               reference for understanding initialization behavior of various
//               SV datatypes.
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

module data_types_def_val_hs;

  reg        reg_type;
  wire       wire_type;        
  integer    integer_type;
  real       real_type;
  time       time_type;
  realtime   realtime_type;
  bit        bit_type;
  byte       byte_type;
  logic      logic_type;
  shortint   shortint_type;
  int        int_type;
  longint    longint_type;
  shortreal  shortreal_type;

  initial begin
    $display("====================================================");
    $display("             BASIC DATA TYPE DEFAULT VALUES         ");
    $display("====================================================");

    $display("reg        = %b", reg_type);
    $display("wire       = %b", wire_type);
    $display("integer    = %0d", integer_type);
    $display("real       = %0f", real_type);
    $display("time       = %0d", time_type);
    $display("realtime   = %0f", realtime_type);
    $display("bit        = %0d", bit_type);
    $display("byte       = %0d", byte_type);
    $display("logic      = %b", logic_type);
    $display("shortint   = %0d", shortint_type);
    $display("int        = %0d", int_type);
    $display("longint    = %0d", longint_type);
    $display("shortreal  = %0f", shortreal_type);

    $display("====================================================");
  end

endmodule
