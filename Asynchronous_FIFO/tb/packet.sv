class packet;
logic w_en, r_en;
logic full, empty;
rand logic [7:0]data_in;
logic [7:0]data_out;


function void print(string name = "");
    $display("++++%0s++++", name);
    $display("w_en = %0d", w_en);
    $display("r_en = %0d", r_en);
    $display("full = %0d", full);
    $display("empty = %0d", empty);
    $display("data_in = %0d", data_in);
    $display("data_out = %0d", data_out);
endfunction
endclass
