class environment;
    generator gen;
    driver dri;
    monitor mon;
    scoreboard scb;
    coverage cov;

    task run();
            gen = new();
            dri = new();
            mon = new();
            scb = new();
            cov = new();
        fork
            gen.run();
            dri.run();
            mon.run();
            cov.run();
            scb.run();
        join_none
        endtask
endclass
