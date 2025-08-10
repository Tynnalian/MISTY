//---------------------------------------------------------
// Class: axis_pipe_dv_pkg
//---------------------------------------------------------

// AXI-Stream pipe verification package.

package axis_misty_pipe_pkg;

    // Import UVM package.
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // import misty_pkg
    import misty_top_pkg::*;
    import misty_pkg::*;
    import axis_misty_dv_pkg::*;
    import reset_agent_pkg::*;

    // Import VIP packages.
    import mvc_pkg::*;
    import mgc_axi4stream_v1_0_pkg::*;
    import mgc_axi4stream_seq_pkg::*;

    parameter DURATION = 42;

    `include "axis_misty_pipe_scoreboard.sv"
    `include "axis_misty_pipe_env.sv"
    `include "axis_misty_test.sv"

endpackage
