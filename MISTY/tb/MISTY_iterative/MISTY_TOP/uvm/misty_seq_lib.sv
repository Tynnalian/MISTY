//---------------------------------------------------------
// Class: misty_seq_base
//---------------------------------------------------------
//
// Base sequence for misty 

class misty_seq_base extends uvm_sequence#(misty_seq_item_base);

    `uvm_object_utils(misty_seq_base)


    int item_amount;


    function new(string name = "");
        super.new(name);  
        configure();      
    endfunction

    //---------------------------------------------------------
    // Function: configure
    //---------------------------------------------------------
    
    // Configure the sequence by reading values from the resource DB

    virtual function void configure();
        void'(uvm_resource_db#(int)::read_by_name("seqr", "item_amount", item_amount));  
        `uvm_info(get_name(), $sformatf("pkt_size = %0d", item_amount), UVM_MEDIUM) 
    endfunction

    //---------------------------------------------------------
    // Task: body
    //---------------------------------------------------------

    // Main task that generates the sequence of items

    virtual task body();
        repeat(item_amount) begin
            req = REQ::type_id::create("req"); 
            start_item(req);                    
            randomize_req();                   
            finish_item(req);                   
        end
    endtask

    //---------------------------------------------------------
    // Function: randomize_req
    //---------------------------------------------------------
    
    // Randomize the request item

    virtual function void randomize_req();
        if(!req.randomize()) `uvm_fatal(get_name(),
            $sformatf("Can't randomize %s", get_name()));  
    endfunction

endclass

//---------------------------------------------------------
// Class: misty_seq_sc
//---------------------------------------------------------

// self_check_seq

class misty_seq_sc extends misty_seq_base;

    `uvm_object_utils(misty_seq_sc)

    // Constructor.

    misty_seq_item_base resp;

    function new(string name = "");
        super.new(name);
    endfunction

    // Task ~body~ impements sequence scenario.

    virtual task body();
        repeat(item_amount) begin
            req = REQ::type_id::create("req");            
            start_item(req);
            randomize_req(); 
            finish_item(req);
            `uvm_info(get_type_name(), $sformatf(
                "REQ_1: %s", req.convert2string()), UVM_DEBUG);
            req = REQ::type_id::create("req");
            get_response(resp);
            `uvm_info(get_type_name(), $sformatf(
                 "RESP: %s", resp.convert2string()), UVM_DEBUG);
            start_item(req);
            req.enc = ~resp.enc;
            req.text_i = resp.text_o;
            req.key = resp.key;
            `uvm_info(get_type_name(), $sformatf(
                "Starting: %s", req.convert2string()), UVM_DEBUG);
            finish_item(req);
            get_response(resp);  
        end
    endtask

endclass