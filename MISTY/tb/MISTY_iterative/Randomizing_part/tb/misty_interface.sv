//---------------------------------------------------------
// Interface: misty_intf
//---------------------------------------------------------

// AXI-Stream interface

interface misty_intf (
    input  logic clk,
    input  logic aresetn
);
   
    
    // Interface wires
    logic         enc_i;
    logic         valid_i;
    logic [63:0]  text_i;
    logic         stall_i;
    logic [255:0] key_i;
    logic         valid_o;      
    logic         ready_o;
    logic [63:0]  text_o;

    // Interface tasks.

    task wait_for_clks(int num);
        repeat(num) @(posedge clk);
    endtask

    task wait_for_reset();
        wait(!aresetn);
    endtask

    task wait_for_unreset();
        wait(aresetn);
    endtask

    function bit is_handshake();
    return valid_i && ready_o;
    endfunction
    


      

property pValidandReadyHandshake;
        @(posedge clk) disable iff (!aresetn )  valid_i && ready_o 

endproperty

   cpHandshake: cover property(pValidandReadyHandshake);

property pValid_iandvalid_o;
        @(posedge clk) disable iff (!aresetn )  valid_i && valid_o

endproperty

   cpvalidandvalid: cover property(pValid_iandvalid_o);

property pValid_ibeforereset;
        @(posedge clk)  valid_i |-> ##1 !aresetn;

endproperty

   cpValidbeforereset: cover property(pValid_ibeforereset);

property pValid_iandstall;
         @(posedge clk) disable iff (!aresetn )  valid_i && stall_i

endproperty

cpVALID_I_STALL: cover property(pValid_iandstall); 

property pValid_iwithstall;
         @(posedge clk) disable iff (!aresetn )   $rose(valid_i) && $rose(stall_i)

endproperty

cpVALID_I_with_STALL: cover property(pValid_iwithstall);



property pValid_oandstall;
         @(posedge clk) disable iff (!aresetn )  $rose(valid_o) && stall_i |-> ##0 valid_o

endproperty

cpVALID_O_STALL: cover property(pValid_oandstall);

apVALID_O_STALL: assert property(pValid_oandstall);




endinterface
