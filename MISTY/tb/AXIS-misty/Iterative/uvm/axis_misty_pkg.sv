//---------------------------------------------------------
// Class: axis_alu_dv_pkg
//---------------------------------------------------------

// AXI-Stream ALU verification package.

package axis_misty_dv_pkg;

    // Import UVM package.
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // import misty_pkg
    import misty_top_pkg::*;
    import misty_pkg::*;
    import axis_misty_params_pkg::*;
    import reset_agent_pkg::*;

    // Import VIP packages.
    import mvc_pkg::*;
    import mgc_axi4stream_v1_0_pkg::*;
    import mgc_axi4stream_seq_pkg::*;

    parameter DURATION = 294;

    `include "axis_misty_defines.svh"
    `include "axis_misty_seq.sv"
    `include "axis_misty_driver.sv"
    `include "axis_misty_monitor.sv"
    `include "axis_misty_scoreboard.sv"
    `include "axis_misty_env.sv"
    `include "axis_misty_test.sv"

endpackage
