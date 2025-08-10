//---------------------------------------------------------
// Class: KS_passthru_driver_base
//---------------------------------------------------------

// KS passthrough driver.

class KS_passthru_driver_base extends KS_driver_base;


    `uvm_component_utils(KS_passthru_driver_base)

    // Passthrough sequence handle.
    
    misty_passthru_seq passthru_seq;

    // KS_python_model

    KS_model  model;

    logic [127:0] key;
    logic [63:0] text;
    logic        enc;
    logic [255:0] expand_keys; 


    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build. Passthrough sequence is extracted from database.

    virtual function void build_phase(uvm_phase phase);
        if(!uvm_resource_db#(misty_passthru_seq)::read_by_name(
            get_full_name(), "passthru_seq", passthru_seq)) begin
            `uvm_fatal(get_name(), "Can't get passthru_seq!");
        end
        model = new();
    endfunction

    // Reset task is overriden for passthrough
    // sequence. Request in passthrough sequence
    // is set to null in this implementation.
    
    virtual task pre_reset_phase(uvm_phase phase);
    endtask

    virtual task reset();
        passthru_seq.req = null;
    endtask

        virtual task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        reset();
        phase.drop_objection(this);
    endtask

    virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            set_data();
            seq_item_port.item_done();
        end
    endtask  



    // Conversion from higher level to the lower
    // level is implemented here.

    virtual task set_data();
        // Divide single high level transaction
        // to the multiple low level transactions.
        misty_seq_item_base misty_req;

        misty_req = misty_seq_item_base::type_id::create("misty_req");

        foreach (key[i]) begin
            model.fill_K(int'(req.key[i]));
        end

        model.key_schedule();

        foreach (expand_keys[i]) begin
            expand_keys[i] = model.get(i);
        end

        model.delete_array();

        if(!std::randomize(text)) begin
            `uvm_fatal(get_name(), "Can't randomize 'text'!");
        end

        if(!std::randomize(enc)) begin
            `uvm_fatal(get_name(), "Can't randomize 'enc'!");
        end


        misty_req.key = expand_keys;
        misty_req.text_i = text;
        misty_req.enc   = enc;
        passthru_seq.req = misty_req;

        wait(passthru_seq.req == null);
    endtask

endclass

//---------------------------------------------------------
// Class: KS_passthru_driver
//---------------------------------------------------------

// KS passthrough driver where enc_i === 1.

class KS_passthru_driver_self_check extends KS_passthru_driver_base;


    `uvm_component_utils(KS_passthru_driver_self_check)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    misty_passthru_seq_sc passthru_seq_sc;

     virtual function void build_phase(uvm_phase phase);
        if(!uvm_resource_db#(misty_passthru_seq_sc)::read_by_name(
            get_full_name(), "passthru_seq_sc", passthru_seq_sc)) begin
            `uvm_fatal(get_name(), "Can't get passthru_seq!");
        end
        model = new();
    endfunction

    virtual task reset();
        passthru_seq_sc.req = null;
    endtask


    virtual task set_data();
        // Divide single high level transaction
        // to the multiple low level transactions.
        misty_seq_item_base misty_req;

        misty_req = misty_seq_item_base::type_id::create("misty_req");

        foreach (key[i]) begin
            model.fill_K(int'(req.key[i]));
        end

        model.key_schedule();

        foreach (expand_keys[i]) begin
            expand_keys[i] = model.get(i);
        end

        model.delete_array();

        if(!std::randomize(text)) begin
            `uvm_fatal(get_name(), "Can't randomize 'text'!");
        end

        misty_req.key = expand_keys;
        misty_req.text_i = text;
        misty_req.enc   = 1;
        passthru_seq_sc.req = misty_req;

        wait(passthru_seq_sc.req == null);

    endtask

endclass
