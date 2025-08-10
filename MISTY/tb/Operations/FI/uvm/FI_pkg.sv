//---------------------------------------------------------
// Class: FI_pkg
//---------------------------------------------------------

// Verification package

package FI_pkg;
    parameter DATA_WIDTH = 8;
    
    // amount of clocks need for computing 
    parameter DURATION = 7; 
   
    import pysv::*;
    import uvm_pkg::*;
    import reset_agent_pkg::*;
    
    `include "uvm_macros.svh" 
    
`include "FI_seq_item.sv"
`include "FI_seq_lib.sv"
`include "FI_driver.sv"
`include "FI_monitor.sv"
`include "FI_agent.sv"
`include "FI_cov.sv"
`include "FI_scoreboard.sv"
`include "FI_env.sv"
`include "FI_test.sv"

endpackage
