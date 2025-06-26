// ===================================================================
// FIFO Verification Environment - Test Bench Module
// ===================================================================
// File: FIFO_tb.sv
// Description: Main test stimulus generator for FIFO verification
//              with multiple test phases and directed scenarios
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

import FIFO_transaction_pkg::*;
import shared_pkg::*;

module fifo_tb(fifo_if.TEST fifoif);
    
    // Test transaction generator
    FIFO_transaction_class fifo_trans;
    
    // Test phase control variables
    int phase_write_cycles = 10;
    int phase_read_cycles = 10;
    int phase_random_cycles = 1000;
    
    // ===================================================================
    // MAIN TEST EXECUTION BLOCK
    // Orchestrates different test phases for comprehensive verification
    // ===================================================================
    initial begin
        // Initialize test environment
        initialize_test_environment();
        
        // Execute systematic test phases
        execute_reset_phase();
        execute_write_fill_phase();
        execute_read_drain_phase();
        execute_random_operation_phase();
        
        // Complete test execution
        complete_test_execution();
    end

    // ===================================================================
    // TEST ENVIRONMENT INITIALIZATION
    // Sets up test components and initial conditions
    // ===================================================================
    task initialize_test_environment();
        $display("\n" + "="*50);
        $display("    FIFO VERIFICATION TEST STARTED");
        $display("="*50);
        $display("Initializing test environment...");
        
        // Create stimulus generator
        fifo_trans = new();
        
        // Set initial interface conditions
        fifoif.rst_n = 1'b0;
        fifoif.wr_en = 1'b0;
        fifoif.rd_en = 1'b0;
        fifoif.data_in = 16'h0000;
        
        $display("Test environment initialized successfully");
    endtask

    // ===================================================================
    // RESET PHASE EXECUTION
    // Verifies proper reset behavior of the FIFO
    // ===================================================================
    task execute_reset_phase();
        $display("\n--- Phase 1: Reset Verification ---");
        $display("Testing FIFO reset functionality...");
        
        // Assert reset for multiple cycles
        fifoif.rst_n = 1'b0;
        repeat(RESET_DURATION) @(negedge fifoif.clk);
        
        // Deassert reset and allow stabilization
        fifoif.rst_n = 1'b1;
        @(negedge fifoif.clk);
        
        $display("Reset phase completed");
    endtask

    // ===================================================================
    // WRITE FILL PHASE EXECUTION
    // Fills FIFO completely to test full condition and overflow
    // ===================================================================
    task execute_write_fill_phase();
        $display("\n--- Phase 2: FIFO Fill Test ---");
        $display("Executing write-only operations to fill FIFO...");
        
        // Configure transaction for write-only operations
        fifo_trans.constraint_mode(0);  // Disable all constraints
        fifo_trans.wr_only.constraint_mode(1);  // Enable write-only
        
        // Execute write operations
        repeat(phase_write_cycles) begin
            // Generate and apply stimulus
            assert(fifo_trans.randomize()) else $fatal("Randomization failed in write phase");
            apply_stimulus_to_interface(fifo_trans);
            @(negedge fifoif.clk);
        end
        
        $display("Write fill phase completed - FIFO should be full");
    endtask

    // ===================================================================
    // READ DRAIN PHASE EXECUTION
    // Drains FIFO completely to test empty condition and underflow
    // ===================================================================
    task execute_read_drain_phase();
        $display("\n--- Phase 3: FIFO Drain Test ---");
        $display("Executing read-only operations to drain FIFO...");
        
        // Configure transaction for read-only operations
        fifo_trans.constraint_mode(0);  // Disable all constraints
        fifo_trans.rd_only.constraint_mode(1);  // Enable read-only
        fifo_trans.data_in.rand_mode(0);  // Disable data randomization for reads
        
        // Execute read operations
        repeat(phase_read_cycles) begin
            // Generate and apply stimulus
            assert(fifo_trans.randomize()) else $fatal("Randomization failed in read phase");
            apply_stimulus_to_interface(fifo_trans);
            @(negedge fifoif.clk);
        end
        
        $display("Read drain phase completed - FIFO should be empty");
    endtask

    // ===================================================================
    // RANDOM OPERATION PHASE EXECUTION
    // Executes random mix of operations for comprehensive testing
    // ===================================================================
    task execute_random_operation_phase();
        $display("\n--- Phase 4: Random Operations Test ---");
        $display("Executing mixed random operations for comprehensive testing...");
        
        // Configure transaction for random operations
        fifo_trans.constraint_mode(0);  // Disable directed constraints
        fifo_trans.wr_only.constraint_mode(0);
        fifo_trans.rd_only.constraint_mode(0);
        fifo_trans.data_in.rand_mode(1);  // Re-enable data randomization
        
        // Execute random operations
        repeat(phase_random_cycles) begin
            // Generate and apply stimulus
            assert(fifo_trans.randomize()) else $fatal("Randomization failed in random phase");
            apply_stimulus_to_interface(fifo_trans);
            @(negedge fifoif.clk);
        end
        
        $display("Random operations phase completed");
    endtask

    // ===================================================================
    // STIMULUS APPLICATION FUNCTION
    // Applies transaction stimulus to the interface
    // ===================================================================
    function void apply_stimulus_to_interface(FIFO_transaction_class transaction);
        fifoif.data_in = transaction.data_in;
        fifoif.rst_n = transaction.rst_n;
        fifoif.wr_en = transaction.wr_en;
        fifoif.rd_en = transaction.rd_en;
    endfunction

    // ===================================================================
    // TEST COMPLETION TASK
    // Finalizes test execution and signals completion
    // ===================================================================
    task complete_test_execution();
        $display("\n--- Test Execution Complete ---");
        $display("All test phases have been executed successfully");
        $display("Signaling test completion to monitor...");
        
        // Signal test completion
        simulation_complete = 1'b1;
        
        // Allow monitor to process final transactions
        repeat(5) @(negedge fifoif.clk);
        
        $display("Test bench execution finished");
        $display("="*50);
    endtask

endmodule
        
