class generator;
    packet pkt;

    task run();
        repeat(10) begin
            pkt=new();
            assert(pkt.randomize());
            common::gen2dri.put(pkt);
            pkt.print("GENERATOR");
        end
        endtask
endclass
