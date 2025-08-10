//---------------------------------------------------------
// Utility: AXI4-Lite VIP  utilities
//---------------------------------------------------------

// UVM object new

`define uvm_object_new \
    function new (string name = ""); \
        super.new( name ); \
    endfunction

// UVM component new

`define uvm_component_new \
    function new(string name , uvm_component parent); \
        super.new(name, parent); \
    endfunction
