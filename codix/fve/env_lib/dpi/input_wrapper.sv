/******************************************************************************
 *         Hardware accelerated Functional Verification of Processor          *
 ******************************************************************************/
/**
 *  \file   input_wrapper.sv
 *  \date   09-03-2013
 *  \brief  input wrapper pass NetCOPE transaction from sender to HW
 *  environment
 */

import dpi_wrapper_pkg::*;


// This class is responsible for taking NetCOPE transactions from input mailbox
// and sending them to HW part of the verification environment through DPI
// layer. Unit must be enabled by "setEnable()" function call. Unit can be 
// stoped by "setDisable()" function call.  
class InputWrapper extends ovm_component;
    
    // Public Class Atributes
    string    inst;      //! Input Wrapper identification
    bit       enabled;   //! Input Wrapper enabling
    bit       busy;      //! Input Wrapper busy signal
 
    // registration of component tools
    `ovm_component_utils_begin( InputWrapper )
        // implements the data operations for an ovm_object based property
        `ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end

    // get port
    ovm_get_port#(NetCOPETransaction) gport;
       
    // Constructor - creates Input Wrapper object
    // \param inst     - Input Wrapper instance name
    // \param inputMbx - transaction mailbox
    function new (string name, ovm_component parent);
      super.new( name, parent );
      pxport = new("pxport", this);

      this.inst        = inst;      //! Store wrapper identifier
      this.enabled     = 0;         //! Input Wrapper is disabled by default
      this.busy        = 0;
    endfunction: new


    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build

    // Enable Input Wrapper - eable wrapper and runs wrapper process
    virtual task setEnabled();
      int res;
      enabled = 1;                 //! Wrapper Enabling
      res = c_openDMAChannel();    //! Open DMA Channel 
      $write("OPENING CHANNEL (musi byt 0): %d\n",res);
      fork
        run();                     //! Creating wrapper subprocess
      join_none;  
    endtask : setEnabled
        
    
    // Disable Input Wrapper
    virtual task setDisabled();
      int res;
      enabled = 0;                 //! Disable Wrapper
      res = c_closeDMAChannel();   //! Close DMA Channel
      $write("CLOSING CHANNEL (musi byt 0): %d\n",res); 
    endtask : setDisabled

    // Run Input Wrapper - receives transactions and sends them through DPI to HW
    task run();
      int res;
      NetCOPETransaction ntr;
      
    while (enabled) begin
        pxport.get(ntr);
        ntr.display();
        res = c_sendData(ntr.data);
        
        // data transfer to hardware through DMA channel
        res = c_sendData(ntr.data);
        if (res!=0) begin
            $error("SEND DATA in input wrapper failed!!!");
            $finish();
        end	      
        busy = 0;
      end
    endtask : run 
 
 endclass : InputWrapper 
