// ===================================================================
// FIFO Verification Environment - Scoreboard Package
// ===================================================================
// File: FIFO_Scoreboard.sv
// Description: Self-checking scoreboard with reference model for
//              FIFO verification and result comparison
// Author: Rana Abdalla
// Date: June 2025
// ===================================================================

package FIFO_Scoreboard_pkg;
    import FIFO_transaction_pkg::*;
    import shared_pkg::*;
    
    class FIFO_Scoreboard_class;
        // Reference model queue to mimic FIFO behavior
        logic [15:0] reference_fifo_queue [$];

        // Expected output values from reference model
        logic [15:0] data_out_ref;
        logic full_ref, empty_ref;
        logic almostfull_ref, almostempty_ref;
        logic underflow_ref, wr_ack_ref, overflow_ref;
        
        // ===================================================================
        // CONSTRUCTOR - Initialize scoreboard statistics
        // ===================================================================
        function new();
            correct_count_global = 0;
            error_count_global = 0;
        endfunction
        
        // ===================================================================
        // MAIN CHECKING FUNCTION
        // Compares DUT outputs with reference model predictions
        // ===================================================================
        function void check_data(FIFO_transaction_class F_txn);
            // Generate expected results using reference model
            reference_model(F_txn);
            
            // Skip checking during reset or initial time
            if ($realtime() > 0) begin
                // Compare all critical outputs between DUT and reference model
                if (F_txn.data_out === data_out_ref && 
                    F_txn.full === full_ref && 
                    F_txn.empty === empty_ref && 
                    F_txn.almostfull === almostfull_ref && 
                    F_txn.almostempty === almostempty_ref) begin
                    
                    // Transaction passed verification
                    correct_count_global++;
                    
                end else begin
                    // Transaction failed verification - log detailed error
                    error_count_global++;
                    display_verification_error(F_txn);
                end
            end
        endfunction

        // ===================================================================
        // REFERENCE MODEL IMPLEMENTATION
        // Mimics expected FIFO behavior for comparison with DUT
        // ===================================================================
        function void reference_model(FIFO_transaction_class F_txn);
            if (F_txn.rst_n == 0) begin
                // Reset condition - clear all states
                full_ref = 1'b0;
                empty_ref = 1'b1;
                almostfull_ref = 1'b0;
                almostempty_ref = 1'b0;
                underflow_ref = 1'b0;
                wr_ack_ref = 1'b0;
                overflow_ref = 1'b0;
                reference_fifo_queue.delete();
            end else begin
                // Normal operation - handle read/write combinations
                handle_fifo_operations(F_txn);
            end

            // Update status flags based on current queue size
            update_status_flags();
        endfunction

        // ===================================================================
        // FIFO OPERATIONS HANDLER
        // Processes different combinations of read and write operations
        // ===================================================================
        function void handle_fifo_operations(FIFO_transaction_class F_txn);
            case ({F_txn.rd_en, F_txn.wr_en})
                2'b11: handle_simultaneous_read_write(F_txn);
                2'b01: handle_write_only_operation(F_txn);
                2'b10: handle_read_only_operation(F_txn);
                2'b00: handle_no_operation();
            endcase
        endfunction

        // ===================================================================
        // SIMULTANEOUS READ AND WRITE OPERATION HANDLER
        // ===================================================================
        function void handle_simultaneous_read_write(FIFO_transaction_class F_txn);
            if (reference_fifo_queue.size() == 0) begin
                // FIFO empty - only write succeeds, read generates underflow
                reference_fifo_queue.push_back(F_txn.data_in);
                wr_ack_ref = 1'b1;
                overflow_ref = 1'b0;
                underflow_ref = 1'b1;
            end else if (reference_fifo_queue.size() == 8) begin
                // FIFO full - only read succeeds, write generates overflow
                data_out_ref = reference_fifo_queue.pop_front();
                underflow_ref = 1'b0;
                overflow_ref = 1'b1;
                wr_ack_ref = 1'b0;
            end else begin
                // Normal case - both operations succeed
                reference_fifo_queue.push_back(F_txn.data_in);
                data_out_ref = reference_fifo_queue.pop_front();
                wr_ack_ref = 1'b1;
                overflow_ref = 1'b0;
                underflow_ref = 1'b0;
            end
        endfunction

        // ===================================================================
        // WRITE-ONLY OPERATION HANDLER
        // ===================================================================
        function void handle_write_only_operation(FIFO_transaction_class F_txn);
            if (reference_fifo_queue.size() < 8) begin
                // Successful write - FIFO not full
                reference_fifo_queue.push_back(F_txn.data_in);
                wr_ack_ref = 1'b1;
                overflow_ref = 1'b0;
            end else begin
                // Failed write - FIFO full, generate overflow
                wr_ack_ref = 1'b0;
                overflow_ref = 1'b1;
            end
        endfunction

        // ===================================================================
        // READ-ONLY OPERATION HANDLER
        // ===================================================================
        function void handle_read_only_operation(FIFO_transaction_class F_txn);
            if (reference_fifo_queue.size() > 0) begin
                // Successful read - FIFO not empty
                data_out_ref = reference_fifo_queue.pop_front();
                underflow_ref = 1'b0;
            end else begin
                // Failed read - FIFO empty, generate underflow
                underflow_ref = 1'b1;
            end
        endfunction

        // ===================================================================
        // NO OPERATION HANDLER
        // ===================================================================
        function void handle_no_operation();
            // Clear all operation flags when no operation is performed
            wr_ack_ref = 1'b0;
            overflow_ref = 1'b0;
            underflow_ref = 1'b0;
        endfunction

        // ===================================================================
        // STATUS FLAGS UPDATE
        // Updates all FIFO status flags based on current queue state
        // ===================================================================
        function void update_status_flags();
            full_ref = (reference_fifo_queue.size() == 8);
            empty_ref = (reference_fifo_queue.size() == 0);
            almostfull_ref = (reference_fifo_queue.size() == 7);
            almostempty_ref = (reference_fifo_queue.size() == 1);
        endfunction

        // ===================================================================
        // ERROR REPORTING FUNCTION
        // Displays detailed error information when verification fails
        // ===================================================================
        function void display_verification_error(FIFO_transaction_class F_txn);
            $display("=== VERIFICATION ERROR DETECTED ===");
            $display("Time: %0t ns", $realtime());
            $display("DUT Outputs:");
            $display("  Data Out: %0d, Full: %0b, Empty: %0b", 
                    F_txn.data_out, F_txn.full, F_txn.empty);
            $display("  Almost Full: %0b, Almost Empty: %0b", 
                    F_txn.almostfull, F_txn.almostempty);
            $display("  Underflow: %0b, Overflow: %0b, Write Ack: %0b", 
                    F_txn.underflow, F_txn.overflow, F_txn.wr_ack);
            $display("Expected Outputs:");
            $display("  Data Out: %0d, Full: %0b, Empty: %0b", 
                    data_out_ref, full_ref, empty_ref);
            $display("  Almost Full: %0b, Almost Empty: %0b", 
                    almostfull_ref, almostempty_ref);
            $display("  Underflow: %0b, Overflow: %0b, Write Ack: %0b", 
                    underflow_ref, overflow_ref, wr_ack_ref);
            $display("Reference Queue Size: %0d", reference_fifo_queue.size());
            $display("===================================");
        endfunction

        // ===================================================================
        // REFERENCE MODEL STATE DISPLAY
        // Utility function for debugging reference model state
        // ===================================================================
        function void print();
            $display("=== Reference Model State ===");
            $display("Queue Contents: %p", reference_fifo_queue);
            $display("Expected Outputs: data=%0d, full=%0b, empty=%0b, almostfull=%0b, almostempty=%0b", 
                    data_out_ref, full_ref, empty_ref, almostfull_ref, almostempty_ref);
            $display("Expected Control: wr_ack=%0b, overflow=%0b, underflow=%0b", 
                    wr_ack_ref, overflow_ref, underflow_ref);
            $display("=============================");
        endfunction
        
    endclass
    
endpackage

