// ===================================================================
// FIFO Verification Environment - Functional Coverage Package
// ===================================================================
// File: FIFO_Coverage.sv
// Description: Comprehensive functional coverage collection for FIFO
//              verification including cross-coverage analysis
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

package FIFO_Coverage_pkg;
    import FIFO_transaction_pkg::*;
    
    class FIFO_Coverage_class;
        // Transaction handle for coverage sampling
        FIFO_transaction_class coverage_transaction; 

        // ===================================================================
        // COMPREHENSIVE COVERAGE GROUP DEFINITION
        // Covers critical FIFO scenarios and state transitions
        // ===================================================================
        covergroup fifo_functional_coverage;
            
            // Individual signal coverage points
            coverpoint coverage_transaction.wr_en {
                bins write_enabled = {1};
                bins write_disabled = {0};
            }
            
            coverpoint coverage_transaction.rd_en {
                bins read_enabled = {1};
                bins read_disabled = {0};
            }
            
            coverpoint coverage_transaction.full {
                bins fifo_full = {1};
                bins fifo_not_full = {0};
            }
            
            coverpoint coverage_transaction.empty {
                bins fifo_empty = {1};
                bins fifo_not_empty = {0};
            }

            // Cross-coverage between write/read operations and control signals
            // This ensures we test all combinations of operations with status flags
            write_read_acknowledge_cross: cross coverage_transaction.wr_en, 
                                               coverage_transaction.rd_en, 
                                               coverage_transaction.wr_ack;
            
            write_read_overflow_cross: cross coverage_transaction.wr_en, 
                                            coverage_transaction.rd_en, 
                                            coverage_transaction.overflow;
            
            write_read_full_cross: cross coverage_transaction.wr_en, 
                                        coverage_transaction.rd_en, 
                                        coverage_transaction.full;
            
            write_read_empty_cross: cross coverage_transaction.wr_en, 
                                         coverage_transaction.rd_en, 
                                         coverage_transaction.empty;
            
            write_read_almost_full_cross: cross coverage_transaction.wr_en, 
                                               coverage_transaction.rd_en, 
                                               coverage_transaction.almostfull;
            
            write_read_almost_empty_cross: cross coverage_transaction.wr_en, 
                                                coverage_transaction.rd_en, 
                                                coverage_transaction.almostempty;
            
            write_read_underflow_cross: cross coverage_transaction.wr_en, 
                                             coverage_transaction.rd_en, 
                                             coverage_transaction.underflow;

            // Advanced cross-coverage for edge cases
            // Covers scenarios like simultaneous read/write with status conditions
            simultaneous_operations_cross: cross coverage_transaction.wr_en, 
                                                coverage_transaction.rd_en, 
                                                coverage_transaction.full, 
                                                coverage_transaction.empty {
                // Ignore impossible combinations
                ignore_bins impossible_full_empty = binsof(coverage_transaction.full) intersect {1} &&
                                                   binsof(coverage_transaction.empty) intersect {1};
            }
            
        endgroup

        // ===================================================================
        // CONSTRUCTOR - Initialize coverage group
        // ===================================================================
        function new();
            fifo_functional_coverage = new();
        endfunction

        // ===================================================================
        // COVERAGE SAMPLING FUNCTION
        // Called by monitor to sample coverage on each transaction
        // ===================================================================
        function void sample_data(FIFO_transaction_class F_txn);
            // Assign transaction to coverage handle and trigger sampling
            coverage_transaction = F_txn;
            fifo_functional_coverage.sample();
        endfunction

        // ===================================================================
        // COVERAGE REPORTING FUNCTION
        // Provides detailed coverage statistics for analysis
        // ===================================================================
        function void report_coverage_statistics();
            $display("=== FIFO Functional Coverage Report ===");
            $display("Overall Coverage: %0.2f%%", fifo_functional_coverage.get_coverage());
            $display("Write Enable Coverage: %0.2f%%", 
                    fifo_functional_coverage.wr_en.get_coverage());
            $display("Read Enable Coverage: %0.2f%%", 
                    fifo_functional_coverage.rd_en.get_coverage());
            $display("Full Flag Coverage: %0.2f%%", 
                    fifo_functional_coverage.full.get_coverage());
            $display("Empty Flag Coverage: %0.2f%%", 
                    fifo_functional_coverage.empty.get_coverage());
            $display("Cross Coverage Statistics:");
            $display("  Write-Read-Ack: %0.2f%%", 
                    fifo_functional_coverage.write_read_acknowledge_cross.get_coverage());
            $display("  Write-Read-Overflow: %0.2f%%", 
                    fifo_functional_coverage.write_read_overflow_cross.get_coverage());
            $display("  Write-Read-Full: %0.2f%%", 
                    fifo_functional_coverage.write_read_full_cross.get_coverage());
            $display("  Write-Read-Empty: %0.2f%%", 
                    fifo_functional_coverage.write_read_empty_cross.get_coverage());
            $display("=======================================");
        endfunction

    endclass
    
endpackage