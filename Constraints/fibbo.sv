/*------------------------------------------------------------
 File Name   : fibbo.sv
 Date        : 2025-12-14
 Description : Fibonacci sequence using post_randomize()
 Author      : Hemanth Sekhar Kothapalli
 Email       : khsekhar9@gmail.com
------------------------------------------------------------*/

class fibbo;

  rand int a[];

  // Constraint only on size and base cases
  constraint c1 {
    a.size() inside {[10:20]};
    a[0] == 0;
    a[1] == 1;
  }

  // Procedural computation after randomization
  function void post_randomize();
    for (int i = 2; i < a.size(); i++) begin
      a[i] = a[i-1] + a[i-2];
    end
  endfunction

endclass


module top;

  fibbo fib;

  initial begin
    fib = new();
    if (!fib.randomize())
      $fatal("Randomization failed");

    $display("Fibonacci array = %0p", fib.a);
  end

endmodule
