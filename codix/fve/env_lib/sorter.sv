/******************************************************************************
 *         Hardware accelerated Functional Verification of Processor          *
 ******************************************************************************/
/**
 *  \file   sorter.sv
 *  \date   09-03-2013
 *  \brief  Sorter splits output signal from HW environment 
 */


// Sorter class 
class Sorter extends ovm_component;

    // registration of component tools
    `ovm_component_utils_begin( Sorter )
        // implements the data operations for an ovm_object based property
//        `ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end

    // synchronization put port
    ovm_put_port#(syncT) syncport;

    // get port - data
    ovm_get_port#(NetCOPETransaction) gport;


    // Constructor - creates new instance of this class
    function new( string name, ovm_component parent );

        super.new( name, parent );

        syncport = new("syncport", this);
        gport    = new("gport", this);


    endfunction : new

    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build

    // Run Sorter - receives transactions from output mailbox and 
    // according to NetCOPE header sends them to proper port
    task run();

        int cntPM = 0;
        int cntRM = 0;
        int cntMM = 0;
        int monitorID;
        longint count;
        syncT str;
        NetCOPETransaction t;


        str = new();
//        t = new();
        str.flag  = 0;

        while(1) begin
            // transaction with number of packets
            syncport.put(str);
            gport.get(t);

            count = getCount(t);

            // transaction with monitor ID
            syncport.put(str);
            gport.get(t);

            monitorID =  t.data[0];

            priority case (monitorID)
            // portout monitor
            8'h01 : begin
                        syncport.put(str);
                        gport.get(t);
                        // cast to codix_ca_output_transaction
                        //portout_pport.put(output_transaction);
                        cntPM++;
                    end
            // register monitor
            8'h02 : begin
                      for (int i=0 ; i < count ; i++) begin
                        syncport.put(str);
                        gport.get(t);
                        // cast to codix_ca_core_regs_transaction
                        //regs_pport.put(regs_transaction);
                        cntRM++;
                      end
                    end
            // memory monitor
            8'h03 : begin
                      for (int i=0 ; i < count ; i++) begin
                        syncport.put(str);
                        gport.get(t);
                        // cast to codix_ca_mem_transaction
                        //mem_pport.put(mem_transaction);
                        cntMM++;
                      end

                      // finish output wrapper
                      str.flag = 1;
                      syncport.put(str);

                      `ovm_info( get_name(), $sformatf("\nportout monitor transactions: %d\n", cntPM), OVM_MEDIUM);
                      `ovm_info( get_name(), $sformatf("\nregister monitor transactions: %d\n", cntRM), OVM_MEDIUM);
                      `ovm_info( get_name(), $sformatf("\nmemory monitor transactions: %d\n", cntMM), OVM_MEDIUM);

                    end         
          // error
          default : begin
                      // finish output wrapper
                      str.flag = 1;
                      syncport.put(str);

                      `ovm_info( get_name(), $sformatf("\nportout monitor transactions: %d\n", cntPM), OVM_MEDIUM);
                      `ovm_info( get_name(), $sformatf("\nregister monitor transactions: %d\n", cntRM), OVM_MEDIUM);
                      `ovm_info( get_name(), $sformatf("\nmemory monitor transactions: %d\n", cntMM), OVM_MEDIUM);

                      `ovm_error( get_name(), "Unknown Monitor ID!\n" );
                    end
          endcase
      end

    endtask : run

    function longint getCount(NetCOPETransaction n);
      return {n.data[0], n.data[1], n.data[2], n.data[3], n.data[4], n.data[5], n.data[6], n.data[7]};
    endfunction


endclass : Sorter
