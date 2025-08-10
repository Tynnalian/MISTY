
// AXI4-Lite MISTY testbench.
// In this testbench we connect AXI4-Lite master VIP to
// AXI4-Lite slave VIP.

module misty_axi4lite_tb;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import axi4lite_misty_pkg::*;

    // Declare clock and reset.

    logic clk_i;
    logic aresetn_i;

    // Declare AXI4-Lite signals.
    // Connect AXI4-Lite master ans slave via them.

    wire                                                  AWVALID_SOC;
    wire [axi4lite_misty_pkg::AXI4_ADDR_WIDTH   - 1:0]    AWADDR_SOC;
    wire                                                  AWREADY_SOC;

    wire                                                  AWVALID_MEMORY;
    wire [axi4lite_misty_pkg::AXI4_ADDR_WIDTH   - 1:0]    AWADDR_MEMORY;
    wire                                                  AWREADY_MEMORY;


    wire                                                  ARVALID_SOC;
    wire [axi4lite_misty_pkg::AXI4_ADDR_WIDTH   - 1:0]    ARADDR_SOC;
    wire                                                  ARREADY_SOC;

    wire                                                  ARVALID_MEMORY;
    wire [axi4lite_misty_pkg::AXI4_ADDR_WIDTH   - 1:0]    ARADDR_MEMORY;
    wire                                                  ARREADY_MEMORY;


    wire                                                  RVALID_SOC;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH   - 1:0]    RDATA_SOC;
    wire [                                        1:0]    RRESP_SOC;
    wire                                                  RREADY_SOC;

   

    wire                                                  RVALID_MEMORY;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH   - 1:0]    RDATA_MEMORY;
    wire [                                        1:0]    RRESP_MEMORY;
    wire                                                  RREADY_MEMORY;
  
    wire                                                  WVALID_SOC;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH   - 1:0]    WDATA_SOC;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH/8 - 1:0]    WSTRB_SOC;
    wire                                                  WREADY_SOC;

     wire                                                 WVALID_MEMORY;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH   - 1:0]    WDATA_MEMORY;
    wire [axi4lite_misty_pkg::AXI4_DATA_WIDTH/8 - 1:0]    WSTRB_MEMORY;
    wire                                                  WREADY_MEMORY;
  
    wire                                                  BVALID_SOC;
    wire [                                           1:0] BRESP_SOC;
    wire                                                  BREADY_SOC;

    wire                                                  BVALID_MEMORY;
    wire [                                           1:0] BRESP_MEMORY;
    wire                                                  BREADY_MEMORY;

    // Generate clock and reset.

    parameter CLK_PERIOD = 10;

    initial begin
        clk_i <= 0;
        forever begin
            #(CLK_PERIOD/2) clk_i = ~clk_i;
        end
    end


    reset_intf rst_intf (clk_i);
    misty_intf intf (clk_i, aresetn_i);
    //---------------------------------------------------------
    // Field: intf_wrapper
    //---------------------------------------------------------
    
    // GPIO interface wrapper.

    gpio_intf_wrapper#(1) enc (clk_i);

    gpio_intf_wrapper#(1) dec (clk_i);

    




    logic  [127:0]  key;

    logic en_enc;
    logic en_dec;

    assign aresetn_i = rst_intf.reset;
    assign key = intf.key_i;
    assign en_enc = enc.gpio;
    assign en_dec = dec.gpio;
    // Declare interface.

    // Declare AXI4-Lite VIP master.
    // There is no special modules for AXI4-Lite.
    // AXI4-Lite is configured from AXI4 via specific
    // settings in environment class.

    axi4_master #(
        .ADDR_WIDTH      ( axi4lite_misty_pkg::AXI4_ADDR_WIDTH      ),
        .RDATA_WIDTH     ( axi4lite_misty_pkg::AXI4_DATA_WIDTH      ),
        .WDATA_WIDTH     ( axi4lite_misty_pkg::AXI4_DATA_WIDTH      ),
        .ID_WIDTH        ( axi4lite_misty_pkg::AXI4_ID_WIDTH        ),
        .USER_WIDTH      ( axi4lite_misty_pkg::AXI4_USER_WIDTH      ),
        .REGION_MAP_SIZE ( axi4lite_misty_pkg::AXI4_REGION_MAP_SIZE ),
        .IF_NAME         ( "AXI4_MASTER_IF"                            ) 
    ) axi4lite_master (
        .ACLK            ( clk_i                                       ),
        .ARESETn         ( aresetn_i                                   ),
        .AWVALID         ( AWVALID_SOC                                     ),
        .AWADDR          ( AWADDR_SOC                                     ),
        .AWREADY         ( AWREADY_SOC                                    ),
        .ARVALID         ( ARVALID_SOC                                    ),
        .ARADDR          ( ARADDR_SOC                                    ),
        .ARREADY         ( ARREADY_SOC                                    ),
        .RVALID          ( RVALID_SOC                                      ),
        .RDATA           ( RDATA_SOC                                      ),
        .RRESP           ( RRESP_SOC                                       ),
        .RREADY          ( RREADY_SOC                                     ),
        .WVALID          ( WVALID_SOC                                      ),
        .WDATA           ( WDATA_SOC                                       ),
        .WSTRB           ( WSTRB_SOC                                       ),
        .WREADY          ( WREADY_SOC                                      ),
        .BVALID          ( BVALID_SOC                                      ),
        .BRESP           ( BRESP_SOC                                      ),
        .BREADY          ( BREADY_SOC                                      )
    );

    // Declare AXI4-Lite VIP slave.
    // There is no special modules for AXI4-Lite.
    // AXI4-Lite is configured from AXI4 via specific
    // settings in environment class.

    axi4_slave #(
        .ADDR_WIDTH      ( axi4lite_misty_pkg::AXI4_ADDR_WIDTH      ),
        .RDATA_WIDTH     ( axi4lite_misty_pkg::AXI4_DATA_WIDTH      ),
        .WDATA_WIDTH     ( axi4lite_misty_pkg::AXI4_DATA_WIDTH      ),
        .ID_WIDTH        ( axi4lite_misty_pkg::AXI4_ID_WIDTH        ),
        .USER_WIDTH      ( axi4lite_misty_pkg::AXI4_USER_WIDTH      ),
        .REGION_MAP_SIZE ( axi4lite_misty_pkg::AXI4_REGION_MAP_SIZE ),
        .IF_NAME         ( "AXI4_SLAVE_IF"                            )
    ) axi4lite_slave ( 
        .ACLK            ( clk_i                                       ),
        .ARESETn         ( aresetn_i                                   ),
        .AWVALID         ( AWVALID_MEMORY                                     ),
        .AWADDR          ( AWADDR_MEMORY                                      ),
        .AWREADY         ( AWREADY_MEMORY                                     ),
        .ARVALID         ( ARVALID_MEMORY                                     ),
        .ARADDR          ( ARADDR_MEMORY                                     ),
        .ARREADY         ( ARREADY_MEMORY                                     ),
        .RVALID          ( RVALID_MEMORY                               ),
        .RDATA           ( RDATA_MEMORY                                ),
        .RRESP           ( RRESP_MEMORY                                ),
        .RREADY          ( RREADY_MEMORY                               ),
        .WVALID          ( WVALID_MEMORY                               ),
        .WDATA           ( WDATA_MEMORY                                ),
        .WSTRB           ( WSTRB_MEMORY                                ),
        .WREADY          ( WREADY_MEMORY                               ),
        .BVALID          ( BVALID_MEMORY                                      ),
        .BRESP           ( BRESP_MEMORY                                      ),
        .BREADY          ( BREADY_MEMORY                                      )
    );
    
    // Declare DUT

    AXI4_Lite_misty_pipelined #(
        .FLASH_ADDR_WIDTH(axi4lite_misty_pkg::AXI4_ADDR_WIDTH),
        .DATA_WIDTH(axi4lite_misty_pkg::AXI4_DATA_WIDTH      ),
        .WSTRB_LEN(axi4lite_misty_pkg::AXI4_DATA_WIDTH/8     )
    )
     DUT (
        .aclk_i(clk_i),
        .aresetn_i(aresetn_i),
        .key_i(key),
        .enable_decryption_i(en_dec),
        .enable_encryption_i(en_enc),
        .wvalid_i (WVALID_SOC    ),
        .wdata_i  (WDATA_SOC     ),
        .wstrb_i  (WSTRB_SOC     ),
        .wready_o (WREADY_SOC    ),
        .wvalid_o (WVALID_MEMORY ),
        .wdata_o  (WDATA_MEMORY  ),
        .wstrb_o  (WSTRB_MEMORY  ),
        .wready_i (WREADY_MEMORY ),
        .rvalid_i (RVALID_MEMORY ),
        .rdata_i  (RDATA_MEMORY  ),
        .rresp_i  (RRESP_MEMORY  ),
        .rready_o (RREADY_MEMORY ),
        .rvalid_o (RVALID_SOC    ),
        .rdata_o  (RDATA_SOC     ),
        .rresp_o  (RRESP_SOC     ),
        .rready_i (RREADY_SOC    ),
        .awvalid_i(AWVALID_SOC   ),
        .awready_o(AWREADY_SOC   ),
        .awaddr_i (AWADDR_SOC    ),
        .awvalid_o(AWVALID_MEMORY),
        .awready_i(AWREADY_MEMORY),
        .awaddr_o (AWADDR_MEMORY ),
        .arvalid_i(ARVALID_SOC   ),
        .araddr_i (ARADDR_SOC    ),
        .arready_o(ARREADY_SOC   ),
        .arvalid_o(ARVALID_MEMORY),
        .araddr_o (ARADDR_MEMORY ),
        .arready_i(ARREADY_MEMORY),
        .bresp_i  (BRESP_MEMORY  ),
        .bvalid_i (BVALID_MEMORY ),
        .bready_o (BREADY_MEMORY ),
        .bvalid_o (BVALID_SOC    ),
        .bresp_o  (BRESP_SOC     ),
        .bready_i (BREADY_SOC    )
    );
    

    // Run test.

    initial begin
        uvm_resource_db#(virtual reset_intf)::set(
        "uvm_test_top.ag.*", "vif", rst_intf);
        uvm_resource_db#(virtual misty_intf)::set(
            "uvm_test_top.env.misty_agent.*", "vif", intf, null
        );
        uvm_resource_db#(virtual gpio_intf)::set(
            "uvm_test_top.*enc_ag.*", "vif", enc.intf);
        uvm_resource_db#(virtual gpio_intf)::set(
            "uvm_test_top.*dec_ag.*", "vif", dec.intf);    
        // Set GPIO bus width.
        // NOTE: Config is created with context in test.
        uvm_resource_db#(int unsigned)::set(
            "uvm_test_top", "width", 1);

        run_test();
    end

    // ((s_tvalid & s_tready)[->8] thoroughout !(m_tvalid & m_tready)) |-> ##1 !s_tready;

    // always_ff @( clock ) begin : blockName
    //     cnt <= // NBA
    // end





endmodule
