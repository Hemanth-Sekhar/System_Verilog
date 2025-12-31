program test;

  environment env;

  initial begin
    env = new();

    // Run environment in parallel
    fork
      env.run();
    join_none

    // Let reset deassert (reset deasserts at 50ns in top)
    #200;

    $display("TEST: finishing simulation");
    $finish;
  end

endprogram

