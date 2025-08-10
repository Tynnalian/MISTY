//---------------------------------------------------------
// Interface: FI_intf
//---------------------------------------------------------

// Interface for FI

interface FI_intf(input logic clk, input logic aresetn);

    logic enable_i;
    logic valid_i;
    logic [15:0] plain_i;
    logic [15:0] key_i;
    logic [15:0] sypher_o;
    logic valid_o;
    logic ready_o;
   

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

property pDuration;
        @(posedge clk) disable iff (!aresetn || !enable_i)  valid_i && ready_o 
        |-> ##(FI_pkg::DURATION) valid_o ;
endproperty

   apXLEN_duration: assert property(pDuration)
      else $error("INCORRECT amount of cycles for computing");

property pON_OFF;
        @(posedge clk) disable iff (!aresetn )  valid_i && !enable_i && !ready_o 
        |-> ##(1) !ready_o && valid_i  ;
endproperty

   apON_OFF: assert property(pON_OFF)
      else $error("Ready is high when enable is low !!!");      


property pValidandReadyHandshake;
        @(posedge clk) disable iff (!aresetn || !enable_i)  valid_i && ready_o 

endproperty

   cpHandshake: cover property(pValidandReadyHandshake);

property pValid_iandvalid_o;
        @(posedge clk) disable iff (!aresetn || !enable_i)  valid_i && valid_o

endproperty

   cpvalidandvalid: cover property(pValid_iandvalid_o);

property pValid_ibeforereset;
        @(posedge clk)  valid_i |-> ##1 !aresetn;

endproperty

   cpValidbeforereset: cover property(pValid_ibeforereset);

property pValid_iwithoutENABLE;
        @(posedge clk)  disable iff (!aresetn)  valid_i  && ! enable_i;

endproperty

   cpValidnotEnable: cover property(pValid_iwithoutENABLE);             


                          
endinterface
