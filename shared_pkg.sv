// ===================================================================
// FIFO Verification Environment - Shared Package
// ===================================================================
// File: shared_pkg.sv
// Description: Global package containing shared variables and types
//              used across the entire verification environment
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

package shared_pkg;
    // Global test statistics tracking
    // These variables maintain the overall test results across all components
    int unsigned error_count_global;      // Total number of detected errors
    int unsigned correct_count_global;    // Total number of correct operations
    bit simulation_complete;              // Flag to indicate test completion

    // FIFO configuration parameters
    parameter int FIFO_DEPTH_PARAM = 8;   // Maximum FIFO capacity
    parameter int DATA_WIDTH_PARAM = 16;  // Width of data bus in bits
    
    // Test control parameters
    parameter int MAX_TEST_CYCLES = 1000; // Maximum simulation cycles
    parameter int RESET_DURATION = 2;     // Reset assertion time in clock cycles
    
endpackage
 