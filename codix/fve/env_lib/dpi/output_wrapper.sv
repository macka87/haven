/******************************************************************************
 *         Hardware accelerated Functional Verification of Processor          *
 ******************************************************************************/
/**
 *  \file   input_wrapper.sv
 *  \date   09-03-2013
 *  \brief  output wrapper takes NetCope transaction from HW and sends it 
 *  to the sorter
 */

 import dpi_wrapper_pkg::*;

// This class is responsible for taking NetCOPE transactions from HW through DPI
// layer and sending them to SW part of the verification environment. Unit must
// be enabled by "setEnable()" function call. Unit can be stoped by 
// "setDisable()" function call.  
class OutputWrapper;

    // Public Class Atributes
    string    inst;      //! Output Wrapper identification
    bit       enabled;   //! Output Wrapper enabling

    // registration of component tools
    `ovm_component_utils_begin( OutputWrapper )
        // implements the data operations for an ovm_object based property
        `ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end
       
    // Constructor - creates Input Wrapper object  
    // \param inst     - Output Wrapper instance name
    // \param ouputMbx - transaction mailbox     
    function new (string name, ovm_component parent, string inst);
      super.new( name, parent );

      this.inst        = inst;      //! Store wrapper identifier
      this.enabled     = 0;         //! Output Wrapper is disabled by default

    endfunction: new

    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build
   
    // Enable Output Wrapper - eable wrapper and runs wrapper process
    virtual task setEnabled();
      enabled = 1;    //! Wrapper Enabling
      fork
        run();        //! Creating wrapper subprocess
      join_none;  
    endtask : setEnabled
        
    // Disable Output Wrapper
    virtual task setDisabled();
      enabled = 0;   //! Disable Wrapper
    endtask : setDisabled

    // Run Output Wrapper - receives transactions through DPI and sends them to SW.
    task run();
      Transaction tr;
      int res;
      int unsigned size;   
      NetCOPETransaction ntr;
      while (enabled) begin 
        size = 0;
        ntr = new();
        ntr.data = new[4096];
        // we call C function (through DPI layer) for data transfer from hw
        res = c_receiveData(size, ntr.data);

        if (res == 1) begin
           $error("RECEIVE DATA in output wrapper failed!!!"); 
           $finish();
        end
        else begin
          if (size > 0) begin
            // store the right size of data
            ntr.size = size;
            $write("received size: %d\n", size);
            ntr.display("OUTPUT NETCOPE TRANSACTION");
            // put received data to output mailbox
            //outputMbx.put(ntr);  
          end
          else begin
            #10ns;
          end
        end  
      end
    endtask : run 
 
 endclass : OutputWrapper 
