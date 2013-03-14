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

    // Public Class Atributes 
//    tTransMbx  outputMbx;  //! Output Transaction Mailbox
//    tTransMbx  mbx[];      //! Output Controllers' Mailboxes
//    int        mbxNum;     //! Number of mailboxes
//    bit        enabled;    //! Sorter enabling
//    bit        busy;       //! Sorter is receiving transaction

    // registration of component tools
    `ovm_component_utils_begin( Sorter )
        // implements the data operations for an ovm_object based property
//        `ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end

    // Constructor - creates new instance of this class
//    function new( string name, ovm_component parent, tTransMbx outputMbx, tTransMbx mbx[], int mbxNum );
    function new( string name, ovm_component parent );

        super.new( name, parent );

        // Create mailbox
//        this.outputMbx = outputMbx;
//        this.mbx       = mbx;
//        this.mbxNum    = mbxNum;
//        this.enabled   = 0;         //! Sorter is disabled by default
//        this.busy      = 0;         //! Sorter is not busy by default 

    endfunction : new

    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build

    // Enable Sorter - enable sorter and runs sorter process   
/*    virtual task setEnabled();
        enabled = 1;  //! Sorter Enabling
        fork         
           run();     //! Creating sorter subprocess
        join_none;    //! Don't wait for ending
    endtask : setEnabled
        
    // Disable Sorter
    virtual task setDisabled();
        enabled = 0;  //! Disable sorter, after receiving last transaction
    endtask : setDisabled*/

    // Run Sorter - receives transactions from output mailbox and 
    // according to NetCOPE header sends them to proper Output controller.
    virtual task run();
        $display("som v sorteri");
/*        NetCOPETransaction ntr;
        Transaction tr;
        int monitorID;
      
        int cnt88 = 0;
        int cntF6 = 0;
        int cntFC = 0;

        while(enabled) begin
            busy = 0;
            outputMbx.get(tr);
            busy = 1;

            $cast(ntr, tr);
            monitorID =  ntr.data[0];

            priority case (monitorID)
            8'h88 : begin
                        cnt88++;
                        //$write("SORTER: COUNTER FL_OUTPUT_CONTROLLER: %d\n", cnt88);             
                        if (cnt88 % 100000 == 0) begin
                            //$write("%d\n",cnt88);
                            #10ns;
                        end
                        mbx[0].put(tr); // FL Output Controller mailbox 
                    end
            8'hF6 : begin
                        cntF6++;
                        //$write("SORTER: COUNTER FL_GEN_OUTPUT_CONTROLLER: %d\n", cntF6);
                        mbx[1].put(tr); // FL Generator Controller mailbox 
                    end         
            8'hAA : mbx[2].put(tr); // Assertion Reporter mailbox
            8'hBB : mbx[3].put(tr); // Signal Reporter mailbox 
            8'hFC : begin
                        cntFC++;
                        //$write("SORTER: COUNTER COVERAGE_REPORTER: %d\n", cntFC);
                        mbx[4].put(tr); // Coverage Reporter mailbox 
                    end          
          default : begin
                        $error("!!!SORTER: Unknown Output Controller Identifier!!!\n");
                        //$write("%x\n", monitorID);
                        $finish();
                    end  
          endcase
      end*/
    endtask : run
endclass : Sorter
