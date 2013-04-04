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
    bit       enabled;   //! Input Wrapper enabling
    bit       busy;      //! Input Wrapper busy signal
 
    // registration of component tools
    `ovm_component_utils_begin( InputWrapper )
        // implements the data operations for an ovm_object based property
        //`ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end

    // get port
    ovm_get_port#(NetCOPETransaction) gport;
       
    // Constructor - creates Input Wrapper object
    function new (string name, ovm_component parent);
      super.new( name, parent );
      gport = new("gport", this);

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

/*      res = c_openDMAChannel();
      if(res != 0) begin
        `ovm_error( get_name(), "Opening channel is not equal to 0!" );
      end

      // Create wrapper subprocess
      fork
        run();
      join_none;*/

      // receiving of transactions
      while(1) begin

        // get port connected to sender.sv
        gport.get(ntr);

        // printout
        if(DEBUG_LEVEL == ALL) begin
          if(ntr.transType == 1) begin
            ntr.display("InputWrapper: START TRANSACTION");
          end
          else if (ntr.transType == 0) begin
            ntr.display("InputWrapper: DATA TRANSACTION");
          end
          else if (ntr.transType == 5) begin
            ntr.display("InputWrapper: CONTROL TRANSACTION");
          end
          else if (ntr.transType == 4) begin
            ntr.display("InputWrapper: STOP TRANSACTION");
            break;
          end
          else begin
            `ovm_error( get_name(), "Unknown transaction!\n" );
          end
        end

      // while
      end
        
/*      // data transfer to hardware through DMA channel
      res = c_sendData(ntr.data);
      if(res != 0) begin
        `ovm_error( get_name(), "Send data failure!" );
         $finish();
      end

      res = c_closeDMAChannel();
      if(res != 0) begin
        `ovm_error( get_name(), "Closing channel is not equal to 0!" );
      end*/

    endtask : run 

 endclass : InputWrapper 
