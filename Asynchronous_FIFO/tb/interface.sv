interface intf();
logic wclk, wrst_n;
logic rclk, rrst_n;
logic w_en, r_en;
logic [7:0] data_in;
logic [7:0] data_out;
logic full, empty;
endinterface
