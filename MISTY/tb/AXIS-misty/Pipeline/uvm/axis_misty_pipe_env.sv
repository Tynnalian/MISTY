//---------------------------------------------------------
// Class: misty_pipe_env_axis
//---------------------------------------------------------

//  misty environment for axis-verison_pipe

class axis_misty_pipe_env extends axis_misty_env;

    `uvm_component_utils(axis_misty_pipe_env)


    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the environment component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------

    // This function is responsible for constructing the components and setting up the environment.
    
    virtual function void build_phase(uvm_phase phase);
        set_type_override_by_type( axis_misty_scoreboard::get_type(), axis_misty_pipe_scoreboard::get_type());
        super.build_phase(phase);   
    endfunction





endclass