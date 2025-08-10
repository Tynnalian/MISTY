//---------------------------------------------------------
// Class: FO_dv_pkg
//---------------------------------------------------------

// VeriFOcation package

package FO_dv_pkg;
    parameter DATA_WIDTH = 8; 
    parameter DURATION = 27; 
   
    import pysv::*;
    import reset_agent_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh" 
    
`include "FO_seq_item.sv"
`include "FO_seq_lib.sv"
`include "FO_driver.sv"
`include "FO_monitor.sv"
`include "FO_agent.sv"
`include "FO_cov.sv"
`include "FO_scoreboard.sv"
`include "FO_env.sv"
`include "FO_test.sv"
endpackage
