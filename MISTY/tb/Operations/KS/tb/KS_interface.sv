//---------------------------------------------------------
// Interface: FI_intf
//---------------------------------------------------------

// Interface for FI

interface KS_intf(input logic clk, input logic aresetn);

    logic valid_i;
    logic [128-1:0] key_i;
    logic [256-1:0] expand_keys_o;
    logic valid_o;

   

task wait_for_clks(int num);
    repeat(num) @(posedge clk);
endtask

task wait_for_reset();
    wait(!aresetn);
endtask

task wait_for_unreset();
    wait(aresetn); 
endtask


property pDuration;
        @(posedge clk) disable iff (!aresetn )  valid_i  
        |-> ##(8) valid_o ;
endproperty

   apXLEN_duration: assert property(pDuration)
      else $error("INCORRECT amount of cycles for computing operation KS");

property pVALID_1_cycle;
        @(posedge clk) disable iff (!aresetn )  valid_i  
        |-> ##(1) !valid_i  ;
endproperty

   apvalid_1_cycle: assert property(pVALID_1_cycle)
      else $error("VALID_I isn't high 1 cycle!!!");      


property pValid_iandValid_o;
        @(posedge clk) disable iff (!aresetn )  valid_i && valid_o

endproperty

   cpvalidandvalid: cover property(pValid_iandValid_o);

property pValid_ibeforereset;
        @(posedge clk)  valid_i |-> ##[1:7] !aresetn;
endproperty

   cpValidbeforereset: cover property(pValid_ibeforereset);


                         
endinterface
