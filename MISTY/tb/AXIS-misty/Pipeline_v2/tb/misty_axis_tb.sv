//---------------------------------------------------------
// Class: tb_axis_misty
//---------------------------------------------------------

module tb_axis_misty;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import axis_misty_pipe_pkg::*;
    import axis_misty_params_pkg::*;

    // Declare clock and reset.

    logic clk_i;
    logic aresetn_i;

    // Declare AXI-Stream signals.

    logic        m_tvalid;
    logic        m_tready;
    logic [199:0] m_tdata;

    logic        s_tvalid;
    logic        s_tready;
    logic [199:0] s_tdata;
    logic [127:0] key;
    logic         enc_i;  // axi_data[0]
    logic         enable; // axi_data [191]

    // Generate clock and reset.

    parameter CLK_PERIOD = 10;

    initial begin
        clk_i <= 0;
        forever begin
            #(CLK_PERIOD/2) clk_i = ~clk_i;
        end
    end

    //---------------------------------------------------------
    // Field: reset_intf
    //---------------------------------------------------------
    
    // Reset interface.

    reset_intf rst_intf (clk_i);
    misty_intf intf (clk_i, aresetn_i);

    assign aresetn_i = rst_intf.reset;
    assign key = m_tdata    [191:64];
    assign enc_i = m_tdata  [192];
    assign enable = m_tdata [193];
    // Declare interface.

    

    // Declare AXI-Stream VIP master.

    axi4stream_master #(
        .AXI4_ID_WIDTH   ( 0                 ),
        .AXI4_USER_WIDTH ( 0                 ),
        .AXI4_DEST_WIDTH ( 0                 ),
        .AXI4_DATA_WIDTH ( WIDTH               ),
        .IF_NAME         ("AXI4STREAM_MASTER")
    ) axis_master ( 
        .ACLK            ( clk_i             ),
        .ARESETn         ( aresetn_i         ),
        .TVALID          ( m_tvalid          ),
        .TDATA           ( m_tdata           ),
        .TSTRB           ( /* NC */          ),
        .TKEEP           ( /* NC */          ),
        .TLAST           ( /* NC */          ),
        .TID             ( /* NC */          ),
        .TUSER           ( /* NC */          ),
        .TDEST           ( /* NC */          ),
        .TREADY          ( m_tready          )
    );

    // Declare AXI-Stream VIP slave.

    axi4stream_slave #(
        .AXI4_ID_WIDTH   ( 0                 ),
        .AXI4_USER_WIDTH ( 0                 ),
        .AXI4_DEST_WIDTH ( 0                 ),
        .AXI4_DATA_WIDTH ( WIDTH               ),
        .IF_NAME         ("AXI4STREAM_SLAVE" )
    ) axis_slave ( 
        .ACLK            ( clk_i             ),
        .ARESETn         ( aresetn_i         ),
        .TVALID          ( s_tvalid          ),
        .TDATA           ( s_tdata           ),
        .TSTRB           ( /* NC */          ),
        .TKEEP           ( /* NC */          ),
        .TLAST           ( /* NC */          ),
        .TID             ( /* NC */          ),
        .TUSER           ( /* NC */          ),
        .TDEST           ( /* NC */          ),
        .TREADY          ( s_tready          )
    );

    // Declare design under test (DUT).

    axi_stream_misty_pipelined_v2 DUT (
        .aclk_i      ( clk_i         ),
        .aresetn_i   ( aresetn_i     ),
        .key_i       ( key           ),
        .enc_i       ( enc_i         ),
        .enable_i    ( enable        ),
        .s_tvalid_i  ( m_tvalid      ),
        .s_tready_o  ( m_tready      ),
        .s_tdata_i   ( m_tdata [63:0]),
        .m_tvalid_o  ( s_tvalid      ),
        .m_tready_i  ( s_tready      ),
        .m_tdata_o   ( s_tdata       )
    );

    // Run test.

    initial begin
      uvm_resource_db#(virtual misty_intf)::set(
            "uvm_test_top.env.agent.*", "vif", intf, null
        );
      uvm_resource_db#(virtual misty_intf)::set(
        "uvm_test_top", "vif", intf, null
        );     

      uvm_resource_db#(virtual reset_intf)::set(
        "uvm_test_top.ag.*", "vif", rst_intf);
      run_test();
    end


endmodule
