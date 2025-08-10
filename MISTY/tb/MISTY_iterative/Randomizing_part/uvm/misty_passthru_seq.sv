// KS-misty passthrough sequence.

class misty_passthru_seq extends uvm_sequence#(misty_seq_item_base);

    `uvm_object_utils(misty_passthru_seq)

    // Constructor.

    function new(string name = "");
        super.new(name);
    endfunction

    // Task ~body~ impements sequence scenario.

    virtual task body();
        forever begin
            wait(req != null);
            start_item(req);
            // `uvm_info(get_type_name(), $sformatf(
            //     "Starting: %s", req.convert2string()), UVM_MEDIUM);
            finish_item(req);
            req = null;
        end
    endtask

endclass
//---------------------------------------------------------
// Class: misty_passtrhu_seq_sc
//---------------------------------------------------------

// self_check_seq

class misty_passthru_seq_sc extends misty_passthru_seq;

    `uvm_object_utils(misty_passthru_seq_sc)

    // Constructor.

    misty_seq_item_base resp;

    function new(string name = "");
        super.new(name);
    endfunction

    // Task ~body~ impements sequence scenario.

    virtual task body();
        forever begin
            wait(req != null);
            start_item(req);
             `uvm_info(get_type_name(), $sformatf(
                 "Starting: %s", req.convert2string()), UVM_MEDIUM);
            finish_item(req);
            get_response(resp);
            req = null;
            wait(req != null);
            req.enc = ~resp.enc;
            req.text_i = resp.text_o;
            req.key = resp.key;
            start_item(req);
            `uvm_info(get_type_name(), $sformatf(
                "Starting: %s", req.convert2string()), UVM_MEDIUM);
            finish_item(req);
            get_response(resp);
            req = null;  
        end
    endtask

endclass
