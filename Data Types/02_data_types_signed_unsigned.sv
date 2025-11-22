// -----------------------------------------------------------------------------
// File Name   : 02_data_types_signed_unsigned.sv
// Date        : 22-11-2025
// Description : Assigns a negative value (-1) to various SystemVerilog datatypes
//               and compares the stored result to determine whether each type 
//               behaves as signed or unsigned based on value preservation.
//
//               This example demonstrates practical signed/unsigned behavior for
//               packed vectors, unpacked types, integer types, real types, time
//               types, and wire nets using simple value-comparison logic.
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
// -----------------------------------------------------------------------------


module data_types_signed_unsigned_hs;

  reg   [1:0] reg_type;
  wire  [1:0] wire_type;
  integer     integer_type;
  real        real_type;
  time        time_type;
  realtime    realtime_type;
  bit   [1:0] bit_type;
  byte        byte_type;
  logic [1:0] logic_type;
  shortint    shortint_type;
  int         int_type;
  longint     longint_type;
  shortreal   shortreal_type;

  assign wire_type = -1;

  initial begin
    reg_type       = -1;
    integer_type   = -1;
    real_type      = -1.0;
    time_type      = -1;
    realtime_type  = -1.0;
    bit_type       = -1;
    byte_type      = -1;
    logic_type     = -1;
    shortint_type  = -1;
    int_type       = -1;
    longint_type   = -1;
    shortreal_type = -1.0;

    $display("reg        : %s", (reg_type       == -1)   ? "signed" : "unsigned");
    $display("wire       : %s", (wire_type      == -1)   ? "signed" : "unsigned");
    $display("integer    : %s", (integer_type   == -1)   ? "signed" : "unsigned");
    $display("real       : %s", (real_type      == -1.0) ? "signed" : "unsigned");
    $display("time       : %s", (time_type      == -1)   ? "signed" : "unsigned");
    $display("realtime   : %s", (realtime_type  == -1.0) ? "signed" : "unsigned");
    $display("bit        : %s", (bit_type       == -1)   ? "signed" : "unsigned");
    $display("byte       : %s", (byte_type      == -1)   ? "signed" : "unsigned");
    $display("logic      : %s", (logic_type     == -1)   ? "signed" : "unsigned");
    $display("shortint   : %s", (shortint_type  == -1)   ? "signed" : "unsigned");
    $display("int        : %s", (int_type       == -1)   ? "signed" : "unsigned");
    $display("longint    : %s", (longint_type   == -1)   ? "signed" : "unsigned");
    $display("shortreal  : %s", (shortreal_type == -1.0) ? "signed" : "unsigned");

    $finish;
  end

endmodule
