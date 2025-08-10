`timescale 1ns/1ps
//---------------------------------------------------------
// Class: misty_tb
//---------------------------------------------------------

module misty_tb;


    import uvm_pkg::*;

    import pysv::*;


    import misty_passthru_pkg::*;
    
    `include "uvm_macros.svh"

    // Declare clock and reset.

    logic clk_i;
    logic aresetn_i;

    parameter DURATION = 285;

   

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

    misty_intf intf (clk_i, aresetn_i);


    property pDuration;
        @(posedge clk_i) disable iff (!aresetn_i)  intf.valid_i && intf.ready_o 
        |-> ##(DURATION) intf.valid_o ;
    endproperty

   apXLEN_duration: assert property(pDuration)
      else $error("INCORRECT amount of cycles");


    int max_delay;

    // Declare design under test (DUT).

    misty_iterative DUT (
        .clk_i              ( clk_i                         ),
        .aresetn_i          ( aresetn_i                     ),
        .enc_i              ( intf.enc_i                    ),
        .key_i              ( intf.key_i                    ),
        .text_i             ( intf.text_i                   ),
        .text_o             ( intf.text_o                   ),
        .valid_i            ( intf.valid_i                  ),
        .valid_o            ( intf.valid_o                  ),
        .ready_o            ( intf.ready_o                  )
    );


initial begin


    uvm_resource_db#(virtual misty_intf)::set(
            "uvm_test_top.env.misty_agent.*", "vif", intf, null
        );
        uvm_resource_db#(virtual misty_intf)::set(
            "uvm_test_top", "vif", intf, null
        );
    

    uvm_resource_db#(virtual reset_intf)::set(
        "uvm_test_top.ag.*", "vif", rst_intf);

    run_test();
    pysv_finalize();
    end

endmodule