//---------------------------------------------------------
// Interface: FO_intf
//---------------------------------------------------------

// Interface for FO

interface FO_intf(input logic clk, input logic aresetn);

    logic valid_i;
    logic [31:0] plain_i;
    logic [47:0] key_I_i;
    logic [63:0] key_O_i;
    logic [31:0] sypher_o;
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
        @(posedge clk) disable iff (!aresetn)  valid_i && ready_o 
        |-> ##(FO_dv_pkg::DURATION) valid_o ;
endproperty

   apXLEN_duration: assert property(pDuration)
      else $error("INCORRECT amount of cycles for computing operation FO");

      

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
                         
endinterface
