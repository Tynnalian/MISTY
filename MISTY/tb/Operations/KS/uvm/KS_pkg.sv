//---------------------------------------------------------
// Class: KS_dv_pkg
//---------------------------------------------------------

// VeriKScation package

package KS_pkg;
    parameter DATA_WIDTH = 8;  
   
    import pysv::*;
    import reset_agent_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh" 
    
`include "KS_seq_item.sv"
`include "KS_seq_lib.sv"
`include "KS_driver.sv"
`include "KS_monitor.sv"
`include "KS_agent.sv"
`include "KS_cov.sv"
`include "KS_scoreboard.sv"
`include "KS_env.sv"
`include "KS_test.sv"
endpackage
