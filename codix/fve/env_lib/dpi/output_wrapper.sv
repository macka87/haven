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
class OutputWrapper extends ovm_component;

    // registration of component tools
    `ovm_component_utils_begin( OutputWrapper )
        // implements the data operations for an ovm_object based property
        //`ovm_field_object( OVM_DEFAULT | OVM_NOCOMPARE | OVM_NOPRINT | OVM_NORECORD | OVM_NOPACK )
    `ovm_component_utils_end

    // synchronization get port
    ovm_get_port#(syncT) syncport;

       
    // Constructor - creates Input Wrapper object  
    function new (string name, ovm_component parent);
      super.new( name, parent );

      syncport = new("syncport", this);

    endfunction: new

    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build
   
    // Run Output Wrapper - receives transactions through DPI and sends them to SW.
    task run();

      int res;
      int unsigned size; 
      NetCOPETransaction ntr;
      syncT str;
      byte unsigned temp[];            // temporary array

      size = 0;
      ntr = new();

      // wait for input wrapper
      syncport.get(str);

/*      while(1) begin

        temp = new[128];

        // we call C function (through DPI layer) for data transfer from hw
        res = c_receiveData(size, temp);

        // data array with accurate size
        ntr.data = new[size];

        // copy data from temporary array to netcope transaction
        for(int i = 0 ; i < size ; i++) begin
          ntr.data[i] = temp[i];
        end

        // clear temporary array
        temp.delete();

        if (res == 1) begin
          `ovm_error( get_name(), "Receive data in output wrapper failed!" );
        end
        else begin
          if (size > 0) begin
            // store the right size of data
            ntr.size = size;
            $write("received size: %d\n", size);

            // printout
            if(DEBUG_LEVEL == ALL) begin
              if(ntr.transType == 1) begin
                ntr.display("OutputWrapper: START TRANSACTION");
              end
              else if (ntr.transType == 0) begin
                ntr.display("OutputWrapper: DATA TRANSACTION");
              end
              else if (ntr.transType == 5) begin
                ntr.display("OutputWrapper: CONTROL TRANSACTION");
              end
              else if (ntr.transType == 4) begin
                ntr.display("OutputWrapper: STOP TRANSACTION");
                break;
              end
              else begin
                `ovm_error( get_name(), "Unknown transaction!\n" );
              end
            end

            break;

            // put received data to output mailbox
            // .put(ntr);  

          end
          else begin
            #10ns;
          end
        end

      end*/

      res = c_closeDMAChannel();
      $write("CLOSING CHANNEL: %d\n",res); 
      if(res != 0) begin
        `ovm_error( get_name(), "Closing channel is not equal to 0!" );
      end


    endtask : run 
 
 endclass : OutputWrapper 
