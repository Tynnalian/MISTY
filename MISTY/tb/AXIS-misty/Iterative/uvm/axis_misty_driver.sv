//---------------------------------------------------------
// Class: misty_driver_axis
//---------------------------------------------------------

// misty driver for axi_stream .

class misty_driver_axis extends misty_driver_base;

    // For every UVM component you must write this line.

    `uvm_component_utils(misty_driver_axis)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

     virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            set_data();
            seq_item_port.item_done();
        end
    endtask


endclass