// ===================================================================
// FIFO Verification Environment - Device Under Test (DUT) - Updated
// ===================================================================
// File: FIFO_DUT_updated.sv
// Description: Synchronous FIFO implementation with comprehensive
//              status flags and error detection mechanisms
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

module FIFO(fifo_interface.DUT fifo_if);

    // FIFO configuration parameters
    parameter int FIFO_CAPACITY = 8;
    localparam int ADDRESS_WIDTH = $clog2(FIFO_CAPACITY);

    // Internal memory array for FIFO storage
    reg [fifo_if.FIFO_DATA_WIDTH-1:0] memory_array [FIFO_CAPACITY-1:0];

    // Pointer registers for circular buffer implementation
    reg [ADDRESS_WIDTH-1:0] write_pointer, read_pointer;
    reg [ADDRESS_WIDTH:0] element_count;  // Extra bit to distinguish full/empty

    // ===================================================================
    // WRITE OPERATION CONTROL BLOCK
    // Handles all write-related logic including acknowledgment and overflow
    // ===================================================================
    always_ff @(posedge fifo_if.clk or negedge fifo_if.reset_n) begin 
        if (!fifo_if.reset_n) begin
            // Reset all write-related signals and pointer
            write_pointer <= '0;
            fifo_if.write_acknowledge <= 1'b0;
            fifo_if.overflow_flag <= 1'b0;
        end 
        else if (fifo_if.write_enable && element_count < FIFO_CAPACITY) begin
            // Successful write operation when FIFO is not full
            memory_array[write_pointer] <= fifo_if.data_input;
            fifo_if.write_acknowledge <= 1'b1;
            fifo_if.overflow_flag <= 1'b0;
            write_pointer <= write_pointer + 1'b1;
        end 
        else if (fifo_if.write_enable && element_count == FIFO_CAPACITY) begin
            // Attempted write to full FIFO - generate overflow
            fifo_if.write_acknowledge <= 1'b0;
            fifo_if.overflow_flag <= 1'b1;
        end 
        else begin
            // No write operation - clear control signals
            fifo_if.write_acknowledge <= 1'b0;
            fifo_if.overflow_flag <= 1'b0;
        end
    end

    // ===================================================================
    // READ OPERATION CONTROL BLOCK
    // Handles all read-related logic including underflow detection
    // ===================================================================
    always_ff @(posedge fifo_if.clk or negedge fifo_if.reset_n) begin
        if (!fifo_if.reset_n) begin
            // Reset read pointer and underflow flag
            read_pointer <= '0;
            fifo_if.underflow_flag <= 1'b0;
        end
        else if (fifo_if.read_enable && element_count != 0) begin
            // Successful read operation when FIFO is not empty
            fifo_if.data_output <= memory_array[read_pointer];
            read_pointer <= read_pointer + 1'b1;
            fifo_if.underflow_flag <= 1'b0;
        end
        else if (fifo_if.read_enable && element_count == 0) begin
            // Attempted read from empty FIFO - generate underflow
            fifo_if.underflow_flag <= 1'b1;
        end
        else begin
            // No read operation - clear underflow flag
            fifo_if.underflow_flag <= 1'b0;
        end
    end

    // ===================================================================
    // ELEMENT COUNT MANAGEMENT BLOCK
    // Tracks the number of valid elements in the FIFO
    // Handles simultaneous read/write operations correctly
    // ===================================================================
    always_ff @(posedge fifo_if.clk or negedge fifo_if.reset_n) begin
        if (!fifo_if.reset_n) begin
            element_count <= '0;
        end
        else begin
            case ({fifo_if.write_enable, fifo_if.read_enable})
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
    assign fifo_if.full_flag = (element_count == FIFO_CAPACITY);
    assign fifo_if.empty_flag = (element_count == 0);
    assign fifo_if.almost_full_flag = (element_count == FIFO_CAPACITY - 1);
    assign fifo_if.almost_empty_flag = (element_count == 1);

    // ===================================================================
    // ASSERTION PROPERTIES FOR VERIFICATION
    // These assertions verify correct FIFO behavior during simulation
    // ===================================================================
    `ifdef ENABLE_ASSERTIONS
        // Property to verify full flag accuracy
        property full_flag_correctness;
            @(posedge fifo_if.clk) disable iff (!fifo_if.reset_n)
            fifo_if.full_flag == (element_count == FIFO_CAPACITY);
        endproperty
        
        // Property to verify empty flag accuracy
        property empty_flag_correctness;
            @(posedge fifo_if.clk) disable iff (!fifo_if.reset_n)
            fifo_if.empty_flag == (element_count == 0);
        endproperty
        
        // Property to verify almost full flag accuracy
        property almost_full_correctness;
            @(posedge fifo_if.clk) disable iff (!fifo_if.reset_n)
            fifo_if.almost_full_flag == (element_count == FIFO_CAPACITY - 1);
        endproperty
        
        // Property to verify almost empty flag accuracy
        property almost_empty_correctness;
            @(posedge fifo_if.clk) disable iff (!fifo_if.reset_n)
            fifo_if.almost_empty_flag == (element_count == 1);
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
