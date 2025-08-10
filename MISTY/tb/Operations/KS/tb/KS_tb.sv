`timescale 1ns/1ps
//---------------------------------------------------------
// Class: KS_extr_tb
//---------------------------------------------------------

module KS_tb;


    import uvm_pkg::*;

    import pysv::*;


    import KS_pkg::*;
    
    `include "uvm_macros.svh"

    // Declare clock and reset.

    logic clk_i;
    logic aresetn_i;

    int delay_for_reset = 1000;
   

    // Generate clock and reset.

    parameter CLK_PERIOD = 10;

    initial begin
        clk_i <= 0;
        forever begin
            #(CLK_PERIOD/2) clk_i = ~clk_i;
        end
    end

    //---------------------------------------------------------
    // Field: reset_intf
    //---------------------------------------------------------
    
    // Reset interface.

    reset_intf rst_intf (clk_i);

    assign aresetn_i = rst_intf.reset;
    // Declare interface.

    KS_intf intf (clk_i, aresetn_i);


    int max_delay;

    // Declare design under test (DUT).

    key_schedule DUT (
        .clk_i              ( clk_i                         ),
        .aresetn_i          ( aresetn_i                     ),
        .key_i              ( intf.key_i                    ),
        .valid_i            ( intf.valid_i                  ),
        .valid_o            ( intf.valid_o                  ),
        .expand_keys_o      (  intf.expand_keys_o           )
    );


initial begin


    uvm_resource_db#(virtual KS_intf)::set(
        "uvm_test_top.env.agent.*", "vif", intf, null
    );
    uvm_resource_db#(virtual KS_intf)::set(
        "uvm_test_top.env.*", "vif", intf, null
    );
    uvm_resource_db#(virtual KS_intf)::set(
        "uvm_test_top", "vif", intf, null
    );    
    uvm_resource_db#(virtual reset_intf)::set(
        "uvm_test_top.ag.*", "vif", rst_intf);

    run_test();
    pysv_finalize();
    end

endmodule
