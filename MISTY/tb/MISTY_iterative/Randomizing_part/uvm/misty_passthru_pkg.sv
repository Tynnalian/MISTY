//---------------------------------------------------------
// Class: misty_passthru_pkg
//---------------------------------------------------------

// misty passthrough verification package.

package misty_passthru_pkg;

     parameter DURATION = 28;

    import uvm_pkg::*;
    import pysv::*;
    import misty_pkg::*;
    import KS_pkg::*;
    import reset_agent_pkg::*;


    `include "uvm_macros.svh"
    `include "misty_passthru_seq.sv"
    `include "KS_passthru_driver.sv"
    `include "KS_passthru_monitor.sv"
    `include "misty_passthru_env.sv"
    `include "misty_passthru_test.sv"

endpackage


