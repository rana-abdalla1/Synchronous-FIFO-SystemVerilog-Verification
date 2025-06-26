// ===================================================================
// FIFO Verification Environment - Transaction Package
// ===================================================================
// File: FIFO_transaction.sv
// Description: Transaction class defining stimulus generation patterns
//              and data structures for FIFO verification
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

package FIFO_transaction_pkg;
    
    class FIFO_transaction_class;
        // Randomizable input stimulus fields
        rand logic [15:0] data_in;              // Data to be written to FIFO
        rand logic rst_n;                       // Reset signal control
        rand logic wr_en;                       // Write operation enable
        rand logic rd_en;                       // Read operation enable
        
        // Output response fields (non-randomizable)
        logic [15:0] data_out;                  // Data read from FIFO
        logic wr_ack;                           // Write success indicator
        logic overflow;                         // Overflow condition
        
        // FIFO status flags
        logic full;                             // FIFO full status
        logic empty;                            // FIFO empty status
        logic almostfull;                       // Almost full status
        logic almostempty;                      // Almost empty status
        logic underflow;                        // Underflow condition
        
        // Configuration parameters for constraint control
        int RD_EN_ON_DIST;                      // Probability of read enable
        int WR_EN_ON_DIST;                      // Probability of write enable
        
        // Constructor with configurable probability distributions
        function new(int RD_EN_ON_dist = 30, int WR_EN_ON_dist = 70);
            this.RD_EN_ON_DIST = RD_EN_ON_dist;
            this.WR_EN_ON_DIST = WR_EN_ON_dist;
        endfunction
        
        // Display function for transaction contents
        function void print();
            $display("=== FIFO Transaction Details ===");
            $display("Inputs:  data_in=%0d, rst_n=%0b, wr_en=%0b, rd_en=%0b", 
                    data_in, rst_n, wr_en, rd_en);
            $display("Outputs: data_out=%0d, wr_ack=%0b, overflow=%0b", 
                    data_out, wr_ack, overflow);
            $display("Status:  full=%0b, empty=%0b, almostfull=%0b, almostempty=%0b, underflow=%0b",
                    full, empty, almostfull, almostempty, underflow);
            $display("================================");
        endfunction
        
        // Constraint for reset signal behavior
        // Reset is rarely asserted to ensure normal operation testing
        constraint reset_signal { 
            rst_n dist {0 := 10, 1 := 90}; 
        }
        
        // Constraint for write enable signal distribution
        constraint wr_signal { 
            wr_en dist {1 := WR_EN_ON_DIST, 
                        0 := (100 - WR_EN_ON_DIST)}; 
        }
        
        // Constraint for read enable signal distribution
        constraint rd_signal { 
            rd_en dist {1 := RD_EN_ON_DIST, 
                        0 := (100 - RD_EN_ON_DIST)}; 
        }
        
        // Directed constraint for write-only operations
        // Used for filling FIFO scenarios
        constraint wr_only { 
            wr_en == 1; 
            rst_n == 1; 
            rd_en == 0; 
        }
        
        // Directed constraint for read-only operations  
        // Used for emptying FIFO scenarios
        constraint rd_only { 
            rd_en == 1; 
            rst_n == 1; 
            wr_en == 0; 
        }
        
    endclass
    
endpackage
