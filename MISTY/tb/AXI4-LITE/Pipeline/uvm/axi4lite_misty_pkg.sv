//---------------------------------------------------------
// Class: axi4lite_loopback_pkg
//---------------------------------------------------------

// AXI4 VIP loopback package.

package axi4lite_misty_pkg;

    // Import UVM package.
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import pysv::*;

    // Import VIP packages.
    import mvc_pkg::*;
    import mgc_axi4_v1_0_pkg::*;
    import mgc_axi4lite_seq_pkg::*;
    import addr_map_pkg::*;
    import rw_txn_pkg::*;

    //Import MISTY packages

    import misty_top_pkg::*;
    import misty_pkg::*;
    import reset_agent_pkg::*;
    import gpio_agent_pkg::*;
    
    `include "axis_misty_driver.sv"
    `include "axis_misty_monitor.sv"


    `include "axi4lite_utils.svh"
    `include "axi4lite_defines.svh"
    `include "axi4lite_seq_lib.sv"
    `include "axi4lite_misty_scrb.sv"
    `include "axi4lite_env.sv"
    `include "axi4lite_testlib.sv"

endpackage
