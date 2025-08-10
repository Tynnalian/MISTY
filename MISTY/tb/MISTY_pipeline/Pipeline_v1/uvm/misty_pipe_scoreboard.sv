//---------------------------------------------------------
// Class: misty_scoreboard_pipe
//---------------------------------------------------------



class misty_scoreboard_pipe extends misty_top_scoreboard;
    
    `uvm_component_utils(misty_scoreboard_pipe)

   


    mailbox#(misty_seq_item_base) valid_in;

    mailbox#(misty_seq_item_base) valid_out;


    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void build_phase(uvm_phase phase);
       super.build_phase(phase);
       valid_in     = new();
       valid_out     = new();
    endfunction

    virtual task reset_phase(uvm_phase phase);
        misty_seq_item_base tmp;
        while(data_in.try_get(tmp));
        while(valid_in.try_get(tmp));
        while(valid_out.try_get(tmp));
    endtask

    virtual task main_phase(uvm_phase phase);
        misty_seq_item_base t_in,t_i,t_o;
        forever begin
            data_in.get(t_in);
              cov_wrapper.sample(t_in);
            if (t_in.valid_i && t_in.valid_o) begin
                t_i=t_in;
                t_o=t_in;
                valid_in.put(t_i);
                valid_out.put(t_o);
            end
            else if (t_in.valid_i) begin
               
                t_i=t_in;
                valid_in.put(t_i);
            end
            else if (t_in.valid_o) begin
                t_o=t_in;

                valid_out.put(t_o);
            end
            if (valid_out.try_get(t_o))  begin
                valid_in.get(t_i);
                t_i.text_o = t_o.text_o;
                 `uvm_info(get_type_name(), $sformatf(
                   "transaction before checking: %s", t_i.convert2string()), UVM_DEBUG);
                do_check(t_i);
            end
        end
    endtask

  
endclass