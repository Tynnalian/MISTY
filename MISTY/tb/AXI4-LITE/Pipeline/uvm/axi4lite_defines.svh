//---------------------------------------------------------
// Parameters: AXI4
//---------------------------------------------------------

parameter AXI4_ADDR_WIDTH      = 33;
parameter AXI4_DATA_WIDTH      = 64;
parameter AXI4_ID_WIDTH        = 1;
parameter AXI4_USER_WIDTH      = 1;
parameter AXI4_REGION_MAP_SIZE = 1;


//---------------------------------------------------------
// Define: AXI4_PARAMS_INST
//---------------------------------------------------------

// AXI4 parameters instance.

`define AXI4_PARAMS_INST \
    .AXI4_ADDRESS_WIDTH   ( AXI4_ADDR_WIDTH      ), \
    .AXI4_RDATA_WIDTH     ( AXI4_DATA_WIDTH      ), \
    .AXI4_WDATA_WIDTH     ( AXI4_DATA_WIDTH      ), \
    .AXI4_ID_WIDTH        ( AXI4_ID_WIDTH        ), \
    .AXI4_USER_WIDTH      ( AXI4_USER_WIDTH      ), \
    .AXI4_REGION_MAP_SIZE ( AXI4_REGION_MAP_SIZE )

//---------------------------------------------------------
// Typedef: axi4_bfm_type
//---------------------------------------------------------

// AXI4 interface with DUT parameters.

typedef virtual mgc_axi4 #(`AXI4_PARAMS_INST) axi4_bfm_type;


//---------------------------------------------------------
// Typedef: axi4_config_t
//---------------------------------------------------------

// AXI4 configuration.

typedef axi4_vip_config #(`AXI4_PARAMS_INST) axi4_config_t;


//---------------------------------------------------------
// Typedef: axi4_agent_t
//---------------------------------------------------------

// AXI4 agent.

typedef axi4_agent #(`AXI4_PARAMS_INST) axi4_agent_t;


//---------------------------------------------------------
// Typedef: axi4_master_delay_t
//---------------------------------------------------------
    
// AXI4 master delay settings.
    
typedef axi4_master_delay_db #(`AXI4_PARAMS_INST) axi4_master_delay_t;


//---------------------------------------------------------
// Typedef: axi4_slave_delay_t
//---------------------------------------------------------

// AXI4 slave delay settings.

typedef axi4_slave_delay_db axi4_slave_delay_t;


//---------------------------------------------------------
// Typedef: axi4_phase_t
//---------------------------------------------------------

// AXI4 phases sequence items.

typedef mvc_sequence_item#(axi4_config_t) axi4_phase_t;


//---------------------------------------------------------
// Typedef: addr_map_t
//---------------------------------------------------------
    
// Address map

typedef addr_map_pkg::address_map addr_map_t;
