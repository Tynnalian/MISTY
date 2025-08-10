`timescale 1ns/1ps
//---------------------------------------------------------
// Class: misty_tb
//---------------------------------------------------------

module misty_top_tb;


    import uvm_pkg::*;

    import pysv::*;


    import misty_pipe_pkg::*;
    
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

    //---------------------------------------------------------
    // Field: reset_intf
    //---------------------------------------------------------
    
    // Reset interface.

    reset_intf rst_intf (clk_i);

    assign aresetn_i = rst_intf.reset;
    // Declare interface.

    misty_intf intf (clk_i, aresetn_i);


    property pDuration;
        @(posedge clk_i) disable iff (!aresetn_i || intf.stall_i )  intf.valid_i && !intf.stall_i 
        |-> ##(misty_pipe_pkg::DURATION) intf.valid_o ;
    endproperty

   apXLEN_duration: assert property(pDuration)
      else $error("INCORRECT amount of cycles while decryption");


     property pSKIP_TRAN;
        @(posedge clk_i) disable iff (!aresetn_i || intf.stall_i )  $rose(intf.valid_i) && $rose(intf.stall_i) 
        |-> ##(misty_pipe_pkg::DURATION) !intf.valid_o ;
    endproperty

   apSKIP_TRAN: assert property(pSKIP_TRAN)
      else $error("not skipping transaction when valid_i && stall_i");   

    generate
    for (genvar i=0; i < DURATION+1; i++) begin: STALL0
        STALL0 : cover property (@(posedge clk_i) disable iff (!aresetn_i) 
          intf.valid_i && !intf.stall_i |-> ## i intf.stall_i);
    end
    endgenerate 

    property pSTALLwhilecomp;
         @(posedge clk_i) disable iff (!aresetn_i )  intf.valid_o |-> ##1 intf.valid_i |-> ## [1:34] intf.stall_i

    endproperty

   cpSTALLwhilecomp: cover property(pSTALLwhilecomp);


    int max_delay;

    // Declare design under test (DUT).

    misty_pipelined DUT (
        .clk_i              ( clk_i                         ),
        .aresetn_i          ( aresetn_i                     ),
        .enc_i              ( intf.enc_i                    ),
        .key_i              ( intf.key_i                    ),
        .text_i             ( intf.text_i                   ),
        .text_o             ( intf.text_o                   ),
        .valid_i            ( intf.valid_i                  ),
        .valid_o            ( intf.valid_o                  ),
        .stall_i            ( intf.stall_i                 )
    );


initial begin


    uvm_resource_db#(virtual misty_intf)::set(
            "uvm_test_top.env.agent.*", "vif", intf, null
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