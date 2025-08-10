// Typedef AXI-Stream VIP agent.

typedef axi4stream_agent #(0, 0, 0, axis_misty_params_pkg::WIDTH) axis_agent_t;

// Typedef AXI-Stream VIP agent config.

typedef axi4stream_vip_config #(0, 0, 0, axis_misty_params_pkg::WIDTH) axis_config_t;

// Typedef AXI-Stream VIP interface.

typedef virtual mgc_axi4stream #(0, 0, 0, axis_misty_params_pkg::WIDTH) axis_if_t;

typedef axi4stream_master_transfer #(0, 0, 0, axis_misty_params_pkg::WIDTH) axis_item_t; 

typedef axi4stream_slave_sequence #(0, 0, 0, axis_misty_params_pkg::WIDTH) slave_seq_t;
