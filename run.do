vlib work
vlog -f src_files.txt
vsim -voptargs=+acc work.top -classdebug -uvmcontrol=all
add wave -position insertpoint  \
sim:/top/fifoif/FIFO_WIDTH \
sim:/top/fifoif/clk \
sim:/top/fifoif/data_in \
sim:/top/fifoif/rst_n \
sim:/top/fifoif/wr_en \
sim:/top/fifoif/rd_en \ 
sim:/top/fifoif/data_out \
sim:/top/MONf/fifo_sb.data_out_ref \
sim:/top/fifoif/wr_ack \
sim:/top/MONf/fifo_sb.wr_ack_ref \
sim:/top/fifoif/overflow \
sim:/top/MONf/fifo_sb.overflow_ref \
sim:/top/fifoif/full \
sim:/top/MONf/fifo_sb.full_ref \
sim:/top/fifoif/empty \
sim:/top/MONf/fifo_sb.empty_ref \
sim:/top/fifoif/almostfull \
sim:/top/MONf/fifo_sb.almostfull_ref \
sim:/top/fifoif/almostempty \
sim:/top/MONf/fifo_sb.almostempty_ref \
sim:/top/fifoif/underflow \
sim:/top/MONf/fifo_sb.underflow_ref \
sim:/top/MONf/fifo_sb.count 
run -all