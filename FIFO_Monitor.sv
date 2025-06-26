// ===================================================================
// FIFO Verification Environment - Monitor Module
// ===================================================================
// File: FIFO_Monitor.sv
// Description: Passive monitor that observes interface signals and
//              coordinates verification components (scoreboard & coverage)
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

import FIFO_transaction_pkg::*;
import FIFO_Scoreboard_pkg::*;
import FIFO_Coverage_pkg::*;
import shared_pkg::*;

module FIFO_Monitor(fifo_if.MONITOR fifoif);
    
    // Verification component instances
    FIFO_transaction_class fifo_trans; 
    FIFO_Coverage_class fifo_cv;
    FIFO_Scoreboard_class fifo_sb;

    // ===================================================================
    // INITIALIZATION BLOCK
    // Creates instances of all verification components
    // ===================================================================
    initial begin
        // Instantiate verification components
        fifo_trans = new();
        fifo_sb = new();
        fifo_cv = new();
        
        $display("=== FIFO Monitor Initialized ===");
        $display("Monitor is observing interface signals...");
        $display("Scoreboard and Coverage collection started");
        $display("===================================");
        
        // Main monitoring loop
        monitor_interface_activity();
    end

    // ===================================================================
    // MAIN MONITORING TASK
    // Continuously monitors interface and processes transactions
    // ===================================================================
    task monitor_interface_activity();
        forever begin
            // Wait for negative edge of clock for stable sampling
            @(negedge fifoif.clk) begin
                // Capture all interface signals into transaction object
                capture_interface_signals();
                
                // Process the captured transaction through verification components
                process_monitored_transaction();
                
                // Check for test completion
                if (simulation_complete) begin
                    display_final_results();
                    $stop;
                end
            end
        end
    endtask

    // ===================================================================
    // SIGNAL CAPTURE FUNCTION
    // Samples all interface signals into transaction object
    // ===================================================================
    function void capture_interface_signals();
        // Input signals to DUT
        fifo_trans.data_in = fifoif.data_in;
        fifo_trans.rst_n = fifoif.rst_n;
        fifo_trans.wr_en = fifoif.wr_en;
        fifo_trans.rd_en = fifoif.rd_en;
        
        // Output signals from DUT
        fifo_trans.data_out = fifoif.data_out;
        fifo_trans.wr_ack = fifoif.wr_ack;
        fifo_trans.overflow = fifoif.overflow;
        
        // Status flags from DUT
        fifo_trans.full = fifoif.full;
        fifo_trans.empty = fifoif.empty;
        fifo_trans.almostfull = fifoif.almostfull;
        fifo_trans.almostempty = fifoif.almostempty;
        fifo_trans.underflow = fifoif.underflow;
    endfunction

    // ===================================================================
    // TRANSACTION PROCESSING
    // Coordinates verification components in parallel
    // ===================================================================
    function void process_monitored_transaction();
        fork
            // Collect functional coverage in parallel
            begin
                fifo_cv.sample_data(fifo_trans);
            end
            
            // Verify transaction correctness in parallel
            begin
                fifo_sb.check_data(fifo_trans);
            end
        join_none  // Non-blocking fork for better performance
    endfunction

    // ===================================================================
    // FINAL RESULTS DISPLAY
    // Shows comprehensive test results at simulation end
    // ===================================================================
    function void display_final_results();
        $display("\n" + "="*60);
        $display("         FIFO VERIFICATION FINAL REPORT");
        $display("="*60);
        $display("Test Execution Summary:");
        $display("  - Total Correct Transactions: %0d", correct_count_global);
        $display("  - Total Error Count: %0d", error_count_global);
        $display("  - Success Rate: %0.2f%%", 
                real'(correct_count_global) / real'(correct_count_global + error_count_global) * 100.0);
        
        if (error_count_global == 0) begin
            $display("  - RESULT: *** ALL TESTS PASSED ***");
        end else begin
            $display("  - RESULT: *** %0d TESTS FAILED ***", error_count_global);
        end
        
        $display("="*60);
        
        // Display coverage report
        fifo_cv.report_coverage_statistics();
        
        $display("Monitor shutdown complete at time %0t", $realtime());
        $display("="*60);
    endfunction

endmodule
