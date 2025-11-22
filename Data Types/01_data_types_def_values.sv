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
