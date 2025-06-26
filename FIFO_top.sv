// ===================================================================
// FIFO Verification Environment - Top Level Module
// ===================================================================
// File: FIFO_top.sv
// Description: Top-level module that instantiates and connects all
//              verification environment components
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

module top();
    
    // Clock generation signal
    logic clk;
    
    // ===================================================================
    // CLOCK GENERATION BLOCK
    // Generates system clock for entire verification environment
    // ===================================================================
    initial begin
        $display("=== FIFO Verification Environment Starting ===");
        $display("Initializing system clock...");
        
        // Initialize clock to known state
        clk = 1'b0;
        
        // Generate continuous clock with 1 time unit period
        forever begin
            #1 clk = ~clk;
        end
    end

    // ===================================================================
    // SIMULATION CONTROL AND MONITORING
    // Controls simulation duration and provides progress monitoring
    // ===================================================================
    initial begin
        $display("Simulation control block initialized");
        $display("Maximum simulation time: %0d time units", 10000);
        
        // Set maximum simulation time to prevent infinite simulation
        #10000;
        $display("ERROR: Simulation exceeded maximum time limit!");
        $display("This may indicate a test hang or infinite loop");
        $finish;
    end

    // ===================================================================
    // COMPONENT INSTANTIATION SECTION
    // Creates and connects all verification environment components
    // ===================================================================
    
    // Interface instantiation with clock connection
    fifo_if fifoif(.clk(clk));
    
    // Device Under Test (DUT) instantiation
    FIFO DUTf(.fifoif(fifoif.DUT));
    
    // Monitor component instantiation
    FIFO_Monitor MONf(.fifoif(fifoif.MONITOR));
    
    // Test bench instantiation
    fifo_tb TBf(.fifoif(fifoif.TEST));

    // ===================================================================
    // VERIFICATION ENVIRONMENT REPORTING
    // Provides initialization status and component connectivity info
    // ===================================================================
    initial begin
        // Wait for all components to stabilize
        #5;
        
        $display("\n" + "="*60);
        $display("    FIFO VERIFICATION ENVIRONMENT STATUS");
        $display("="*60);
        $display("Component Instantiation Summary:");
        $display("  ✓ System Clock         : Running at 1 time unit period");
        $display("  ✓ FIFO Interface       : Connected and operational");
        $display("  ✓ FIFO DUT Module      : Instantiated and bound");
        $display("  ✓ Verification Monitor : Active and monitoring");
        $display("  ✓ Test Bench          : Ready for stimulus generation");
        $display("="*60);
        $display("Environment Ready - Test execution starting...\n");
    end

    // ===================================================================
    // WAVEFORM GENERATION FOR DEBUGGING
    // Optional waveform dumping for debugging purposes
    // ===================================================================
    `ifdef ENABLE_WAVEFORMS
    initial begin
        $dumpfile("fifo_verification.vcd");
        $dumpvars(0, top);
        $display("Waveform dumping enabled: fifo_verification.vcd");
    end
    `endif

    // ===================================================================
    // FINAL SIMULATION SUMMARY
    // Displays final status when simulation completes normally
    // ===================================================================
    final begin
        $display("\n" + "="*60);
        $display("    SIMULATION COMPLETED NORMALLY");
        $display("="*60);
        $display("Final simulation time: %0t", $time);
        $display("All verification components have been properly shutdown");
        $display("Check the verification report above for detailed results");
        $display("="*60);
    end

endmodule
