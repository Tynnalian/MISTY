`timescale 1ns/1ps
//---------------------------------------------------------
// Class: FI_extr_tb
//---------------------------------------------------------

module FI_tb;


    import uvm_pkg::*;

    import pysv::*;


    import FI_pkg::*;
    
    `include "uvm_macros.svh"

    // Declare clock and reset.

    logic clk_i;
    logic aresetn_i;

   

    // Generate clock and reset.

    parameter CLK_PERIOD = 10;

    initial begin
        clk_i <= 0;
        forever begin
            #(CLK_PERIOD/2) clk_i = ~clk_i;
        end
    end


    // Declare interface.

    FI_intf intf (clk_i, aresetn_i);

    //---------------------------------------------------------
    // Field: reset_intf
    //---------------------------------------------------------
    
    // Reset interface.

    reset_intf rst_intf (clk_i);

    assign aresetn_i = rst_intf.reset;

    int max_delay;

    // Declare design under test (DUT).

    FI DUT (
        .clk_i              ( clk_i         ),
        .aresetn_i          ( aresetn_i     ),
        .plain_i            ( intf.plain_i  ),
        .key_i              ( intf.key_i    ),
        .valid_i            ( intf.valid_i  ),
        // .enable_i           ( intf.enable_i               ),
        .ready_o            ( intf.ready_o  ),
        .valid_o            ( intf.valid_o  ),
        .sypher_o           ( intf.sypher_o )
    );


initial begin

    uvm_resource_db#(virtual FI_intf)::set(
        "uvm_test_top.env.agent.*", "vif", intf, null
    );
    uvm_resource_db#(virtual FI_intf)::set(
        "uvm_test_top.env.*", "vif", intf, null
    );
    uvm_resource_db#(virtual FI_intf)::set(
        "uvm_test_top", "vif", intf, null
    );
    uvm_resource_db#(virtual reset_intf)::set(
        "uvm_test_top.ag.*", "vif", rst_intf);

    run_test();
    pysv_finalize();
    end

endmodule
