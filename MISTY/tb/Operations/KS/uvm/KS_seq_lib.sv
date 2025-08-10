//---------------------------------------------------------
// Class: KS_seq_base
//---------------------------------------------------------
//
// Base sequence for KS 

class KS_seq_base extends uvm_sequence#(KS_seq_item_base);

    `uvm_object_utils(KS_seq_base)


    int item_amount;


    function new(string name = "");
        super.new(name);  
        configure();      
    endfunction

    //---------------------------------------------------------
    // Function: configure
    //---------------------------------------------------------
    
    // ConKSgure the sequence by reading values from the resource DB

    virtual function void configure();
        void'(uvm_resource_db#(int)::read_by_name("seqr", "item_amount", item_amount));  
        `uvm_info(get_name(), $sformatf("pkt_size = %0d", item_amount), UVM_LOW) 
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
