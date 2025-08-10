//---------------------------------------------------------
// Class: misty_pipe_pkg
//---------------------------------------------------------

// misty pipe verification package.

package misty_pipe_pkg;
    
    parameter DURATION = 34;

    import uvm_pkg::*;
    import misty_top_pkg::*;
    import misty_pkg::*;
    import reset_agent_pkg::*;


    `include "uvm_macros.svh"
    `include "misty_pipe_driver_lib.sv"
    `include "misty_pipe_monitor.sv"
    `include "misty_pipe_scoreboard.sv"
    `include "misty_env_pipe.sv" 
    `include "misty_test_pipe.sv"

endpackage