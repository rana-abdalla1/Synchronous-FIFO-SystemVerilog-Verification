// ===================================================================
// FIFO Verification Environment - Device Under Test (DUT)
// ===================================================================
// File: FIFO.sv
// Description: Synchronous FIFO implementation with comprehensive
//              status flags and error detection mechanisms
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

module FIFO(fifo_if.DUT fifoif);

    // FIFO configuration parameters
    parameter int FIFO_CAPACITY = 8;
    localparam int ADDRESS_WIDTH = $clog2(FIFO_CAPACITY);

    // Internal memory array for FIFO storage
    reg [fifoif.FIFO_WIDTH-1:0] memory_array [FIFO_CAPACITY-1:0];

    // Pointer registers for circular buffer implementation
    reg [ADDRESS_WIDTH-1:0] write_pointer, read_pointer;
    reg [ADDRESS_WIDTH:0] element_count;  // Extra bit to distinguish full/empty

    // ===================================================================
    // WRITE OPERATION CONTROL BLOCK
    // Handles all write-related logic including acknowledgment and overflow
    // ===================================================================
    always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin 
        if (!fifoif.rst_n) begin
            // Reset all write-related signals and pointer
            write_pointer <= '0;
            fifoif.wr_ack <= 1'b0;
            fifoif.overflow <= 1'b0;
        end 
        else if (fifoif.wr_en && element_count < FIFO_CAPACITY) begin
            // Successful write operation when FIFO is not full
            memory_array[write_pointer] <= fifoif.data_in;
            fifoif.wr_ack <= 1'b1;
            fifoif.overflow <= 1'b0;
            write_pointer <= write_pointer + 1'b1;
        end 
        else if (fifoif.wr_en && element_count == FIFO_CAPACITY) begin
            // Attempted write to full FIFO - generate overflow
            fifoif.wr_ack <= 1'b0;
            fifoif.overflow <= 1'b1;
        end 
        else begin
            // No write operation - clear control signals
            fifoif.wr_ack <= 1'b0;
            fifoif.overflow <= 1'b0;
        end
    end

    // ===================================================================
    // READ OPERATION CONTROL BLOCK
    // Handles all read-related logic including underflow detection
    // ===================================================================
    always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin
        if (!fifoif.rst_n) begin
            // Reset read pointer and underflow flag
            read_pointer <= '0;
            fifoif.underflow <= 1'b0;
        end
        else if (fifoif.rd_en && element_count != 0) begin
            // Successful read operation when FIFO is not empty
            fifoif.data_out <= memory_array[read_pointer];
            read_pointer <= read_pointer + 1'b1;
            fifoif.underflow <= 1'b0;
        end
        else if (fifoif.rd_en && element_count == 0) begin
            // Attempted read from empty FIFO - generate underflow
            fifoif.underflow <= 1'b1;
        end
        else begin
            // No read operation - clear underflow flag
            fifoif.underflow <= 1'b0;
        end
    end

    // ===================================================================
    // ELEMENT COUNT MANAGEMENT BLOCK
    // Tracks the number of valid elements in the FIFO
    // Handles simultaneous read/write operations correctly
    // ===================================================================
    always_ff @(posedge fifoif.clk or negedge fifoif.rst_n) begin
        if (!fifoif.rst_n) begin
            element_count <= '0;
        end
        else begin
            case ({fifoif.wr_en, fifoif.rd_en})
                2'b10: begin  // Write only
                    if (element_count < FIFO_CAPACITY)
                        element_count <= element_count + 1'b1;
                end
                2'b01: begin  // Read only
                    if (element_count != 0)
                        element_count <= element_count - 1'b1;
                end
                2'b11: begin  // Simultaneous read and write
                    if (element_count == FIFO_CAPACITY)
                        element_count <= element_count - 1'b1;  // Read only (FIFO full)
                    else if (element_count == 0)
                        element_count <= element_count + 1'b1;  // Write only (FIFO empty)
                    // For other cases, count remains same (read and write cancel out)
                end
                default: begin  // No operation
                    element_count <= element_count;
                end
            endcase
        end
    end

    // ===================================================================
    // STATUS FLAG GENERATION
    // Combinational logic for all FIFO status indicators
    // ===================================================================
    assign fifoif.full = (element_count == FIFO_CAPACITY);
    assign fifoif.empty = (element_count == 0);
    assign fifoif.almostfull = (element_count == FIFO_CAPACITY - 1);
    assign fifoif.almostempty = (element_count == 1);

    // ===================================================================
    // ASSERTION PROPERTIES FOR VERIFICATION
    // These assertions verify correct FIFO behavior during simulation
    // ===================================================================
    `ifdef ENABLE_ASSERTIONS
        // Property to verify full flag accuracy
        property full_flag_correctness;
            @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            fifoif.full == (element_count == FIFO_CAPACITY);
        endproperty
        
        // Property to verify empty flag accuracy
        property empty_flag_correctness;
            @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            fifoif.empty == (element_count == 0);
        endproperty
        
        // Property to verify almost full flag accuracy
        property almost_full_correctness;
            @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            fifoif.almostfull == (element_count == FIFO_CAPACITY - 1);
        endproperty
        
        // Property to verify almost empty flag accuracy
        property almost_empty_correctness;
            @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            fifoif.almostempty == (element_count == 1);
        endproperty

        // Assert all properties
        assert_full_flag: assert property(full_flag_correctness)
            else $error("FIFO full flag assertion failed at time %0t", $time);
            
        assert_empty_flag: assert property(empty_flag_correctness)
            else $error("FIFO empty flag assertion failed at time %0t", $time);
            
        assert_almost_full: assert property(almost_full_correctness)
            else $error("FIFO almost full flag assertion failed at time %0t", $time);
            
        assert_almost_empty: assert property(almost_empty_correctness)
            else $error("FIFO almost empty flag assertion failed at time %0t", $time);
    `endif

endmodule