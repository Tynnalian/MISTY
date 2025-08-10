module hello_world();
    
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    class hello_world_test extends uvm_test;
        `uvm_component_utils(hello_world_test)

        function new(string name = "", uvm_component parent = null);
            super.new(name, parent);    
        endfunction

        virtual task main_phase(uvm_phase phase);
            string str;
            `ifdef PRINT_MY_STRING
                uvm_cmdline_processor clp = uvm_cmdline_processor::get_inst;
                void'(clp.get_arg_value("+my_string=", str));
            `else
                str = "Hello_World!";
            `endif
            `uvm_info(get_name(), str, UVM_NONE);
        endtask

    endclass

    initial begin
        run_test();
    end

endmodule