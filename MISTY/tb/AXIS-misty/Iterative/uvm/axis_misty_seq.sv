// AXI-Stream misty sequence.

class axis_misty_seq_base extends axi4stream_no_last_deparam_seq;

    // For every UVM object you must write this line.

    `uvm_object_utils(axis_misty_seq_base)

    // Constructor.

    function new(string name = "");
        super.new(name);
    endfunction

    // Add minimal packet size constraint.
    // In original the sequence minimal
    // packet size is 0.

    constraint packet_min_size_c {
        payload.size() > max_pkt_size/2;
    }

endclass
