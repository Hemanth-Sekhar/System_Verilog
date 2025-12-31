vlog +incdir+./rtl tb/fifo.svh

vsim top -vopt -voptargs=+acc
add wave sim:/top/dut/*
run -all
