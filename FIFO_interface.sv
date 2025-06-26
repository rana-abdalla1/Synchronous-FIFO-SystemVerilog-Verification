// ===================================================================
// FIFO Verification Environment - Interface Definition
// ===================================================================
// File: FIFO_interface.sv
// Description: SystemVerilog interface defining the communication
//              protocol between the FIFO DUT and verification components
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

interface fifo_if(input logic clk);
    // Interface configuration parameters
    parameter int FIFO_WIDTH = 16;
    
    // Input signals to FIFO
    logic [FIFO_WIDTH-1:0] data_in;      // Data to be written to FIFO
    logic rst_n;                         // Active-low asynchronous reset
    logic wr_en;                         // Write operation enable
    logic rd_en;                         // Read operation enable
    
    // Output signals from FIFO
    logic [FIFO_WIDTH-1:0] data_out;     // Data read from FIFO
    logic wr_ack;                        // Write operation successful
    logic overflow;                      // FIFO overflow condition
    
    // Status flags from FIFO
    logic full;                          // FIFO is completely full
    logic empty;                         // FIFO is completely empty
    logic almostfull;                    // FIFO has one slot remaining
    logic almostempty;                   // FIFO has only one element
    logic underflow;                     // FIFO underflow condition

    // Modport for Device Under Test (DUT) - FIFO module
    // Defines which signals are inputs and outputs from DUT perspective
    modport DUT (
        input  clk, rst_n, wr_en, rd_en, data_in,
        output data_out, wr_ack, overflow, full, 
               empty, almostfull, almostempty, underflow
    );
    
    // Modport for Test Environment
    // Defines signal directions from testbench perspective
    modport TEST (
        input  clk, data_out, wr_ack, overflow, full,
               empty, almostfull, almostempty, underflow,
        output rst_n, wr_en, rd_en, data_in
    );
    
    // Modport for Monitor Component
    // Monitor observes all signals but doesn't drive any
    modport MONITOR (
        input  clk, data_out, wr_ack, overflow, full,
               empty, almostfull, almostempty, underflow,
               rst_n, wr_en, rd_en, data_in
    );
    
endinterface
