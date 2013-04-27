//  ---------------------------------------------------------
//  Hardware accelerated Functional Verification of Processor
//  ---------------------------------------------------------

//  \file   sender.sv
//  \date   09-03-2013
//  \brief  Sender merge input signal from SW environment 
  
// This class is responsible for loading input program and its encapsulation with
// NetCOPE header. Then NetCOPE transaction are sent to input wrapper through
// tlm_fifo
class Sender extends ovm_component; 
 
    // Public Class Atributes 
    const int pDataWidth; // protocol data width
    int controlTrs;       // number of sent control transactions
    int dataTrs;          // number of sent data transactions

    // put port
    ovm_put_port#(NetCOPETransaction) pport;

    // registration of component tools
    `ovm_component_utils_begin( Sender )
    `ovm_component_utils_end

    // Constructor - creates new instance of this class
    function new( string name, ovm_component parent);
        super.new( name , parent);

        // put port for connection with input wrapper
        pport = new("pport", this);

        this.pDataWidth = 64;
        this.controlTrs = 0;
        this.dataTrs  = 0;

    endfunction : new

    // build - instantiates child components
    function void build;
        super.build();
    endfunction: build

    // time-consuming task
    task run ();
    
        // initialize connection
        sendStart();

        // send input program
        createNetCOPETrans();

        // end of connection
        sendStop();

        // debug printout
        if(DEBUG_LEVEL == INFO || DEBUG_LEVEL == ALL) begin
          `ovm_info( get_name(), $sformatf("\nINPUT\ncontrol transactions: %d\ndata transcations: %d\n", this.controlTrs, this.dataTrs), OVM_MEDIUM);
        end
 
    endtask: run

    // ========================================================================
    // ==  Create NetCOPE transaction from input program by calling
    // ==  functions createDataTransaction and createControlTransaction
    // ========================================================================
    task createNetCOPETrans();
        int fd;                        // input file descriptor
        int index;                     // line index
        string input_program[int];     // associative array for input program

        index = 0;

        // load input program from xexe directory
        fd = $fopen( "xexes/sha.c.xexe.hw", "r" );
        if(fd == 0) begin
            `ovm_error( get_name(), "'sender.sv': Cannot open input program file!\n" );
        end

        // loop over lines of input program
        while(!$feof(fd)) begin
            string line;
            if($fgets(line, fd)) begin
                // save line to associative array
                input_program[index] = line;
                index++;
            end
        end
        
        $fclose(fd);

        createControlTransaction(input_program);

        // create transaction from loaded file with program
//        for(int i = 0; i < input_program.num; i++) begin
        for(int i = 0; i < 10 ; i+=2) begin

            // last transaction
            if(i == (input_program.num-1)) begin
                createDataTransaction(input_program, 1, 1, i);
            end
            // all transactions except last
            else begin
                createDataTransaction(input_program, 0, 1, i);
            end
        end

    endtask : createNetCOPETrans

    // ========================================================================
    // ==  Create NetCOPE data transaction from input program
    // \param input_program - associative array with input program
    // \param lastPart      - last part data flag
    // \param allData       - all data flag
    // \param part          - index for associative array with input program
    // ========================================================================
    task createDataTransaction(input string input_program[int], 
                              input bit lastPart,
                              input bit allData,
                              input int part);
      
      NetCOPETransaction dataTrans = new();

      const int NetCOPE_hdr_size = 8;
      const int data_size = 8;
      int size;
      int second_half = 0;
      int start_pos = 0;
      int end_pos = 7;
      string octet;

      // last part of data
      if(lastPart == 1) begin
          // odd number of lines - last data transaction with half of data
          if(input_program.num%2 == 1) begin
              size = NetCOPE_hdr_size+data_size/2;
          end
      end
      // all parts except last
      else begin
          size = NetCOPE_hdr_size+data_size;
      end

      // NetCOPE transaction settings
      dataTrans.endpointID  = 0;
      dataTrans.transType   = 0;  // data transaction
      dataTrans.ifcProtocol = 1;  // identifies FrameLink protocol
      dataTrans.ifcInfo     = 2*allData + lastPart;  
      
      // NetCOPE transaction transported data  
      dataTrans.data = new[size];
      
      // NetCOPE header
      dataTrans.data[0] = 0;                    // endpointID
      dataTrans.data[1] = 0;                    // endpointProtocol
      dataTrans.data[2] = 0; 
      dataTrans.data[3] = 0;
      dataTrans.data[4] = 0;                    // transType
      dataTrans.data[5] = 0;
      dataTrans.data[6] = 1;                    // ifcProtocol
      dataTrans.data[7] = 2*allData + lastPart; // ifcInfo
      

      // data
      for (int i=8; i<size ; i++) begin
        octet = input_program[part+second_half].substr(start_pos, end_pos);
        dataTrans.data[i] = octet.atobin;

        // second half of data flag
        if(i == 11) begin
            second_half = 1;
            // init positions
            start_pos = 0;
            end_pos = 7;
            continue;
        end

        start_pos += 8;
        end_pos += 8;
      end

      //dataTrans.display("DATA");
      pport.put(dataTrans);    // send data transaction to input wrapper
      this.dataTrs++;

    endtask : createDataTransaction
    
/*    // ========================================================================
    // ==  Create NetCOPE data transaction from input program
    // \param input_program - associative array with input program
    // \param lastPart      - last part data flag
    // \param allData       - all data flag
    // \param part          - index for associative array with input program
    // ========================================================================
    task createDataTransaction(input string input_program[int], 
                               input bit lastPart,
                               input bit allData,
                               input int part);
      
      NetCOPETransaction dataTrans = new();

      const int data_size = 8;
      int size;
      int second_half = 0;
      int start_pos = 0;
      int end_pos = 7;
      string octet;

      // last part of data
      if(lastPart == 1) begin
          // odd number of lines - last data transaction with half of data
          if(input_program.num%2 == 1) begin
              size = data_size/2;
          end
      end
      // all parts except last
      else begin
          size = data_size;
      end

      // NetCOPE transaction settings
      dataTrans.endpointID  = 0;
      dataTrans.transType   = 0;  // data transaction
      dataTrans.ifcProtocol = 1;  // identifies FrameLink protocol
      dataTrans.ifcInfo     = 2*allData + lastPart;  
      
      // NetCOPE transaction transported data  
      dataTrans.data = new[size];
      
      // data
      for (int i=0; i<size ; i++) begin
        octet = input_program[part+second_half].substr(start_pos, end_pos);
        dataTrans.data[i] = octet.atobin;

        // second half of data flag
        if(i == 3) begin
            second_half = 1;
            // init positions
            start_pos = 0;
            end_pos = 7;
            continue;
        end

        start_pos += 8;
        end_pos += 8;
      end

      //dataTrans.display("DATA");
      pport.put(dataTrans);    // send data transaction to input wrapper
      this.dataTrs++;

    endtask : createDataTransaction*/ 
     
    // ========================================================================
    // ==  Create NetCOPE control transaction
    // \param tr - associative array with input program
    // \param part - index into associative array with input program
    // ========================================================================
    task createControlTransaction(input string tr[int]);
       //                           input int part);
      NetCOPETransaction controlTrans = new();
      
      controlTrans.endpointID  = 0;
      controlTrans.transType   = 0;  // data header transaction
      controlTrans.ifcProtocol = 1;  // identifies FrameLink protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      controlTrans.data    = new[8];
      
      // NetCOPE header
      controlTrans.data[0] = 0;  // endpointID
      controlTrans.data[1] = 0;  // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 0;  // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 1;  // ifcProtocol
      controlTrans.data[7] = 0;  // ifcInfo
      
      //controlTrans.display("CONTROL");
      pport.put(controlTrans);   // send control transaction to input wrapper
      this.controlTrs++;

    endtask : createControlTransaction
    

    // ========================================================================
    // ==  Sends start NetCOPE control transaction to HW
    // ========================================================================
    virtual task sendStart();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.data    = new[8];
      
      // NetCOPE header
      controlTrans.data[0] = 0;  // endpointID
      controlTrans.data[1] = 0;   // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 1;   // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 0;   // ifcProtocol
      controlTrans.data[7] = 0;   // ifcInfo
      
      controlTrans.endpointID  = 0;
      controlTrans.transType   = 1;  // control start transaction
      controlTrans.ifcProtocol = 1;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("START CONTROL");
      pport.put(controlTrans);
      this.controlTrs++;

    endtask : sendStart
    
 
    // ========================================================================
    // ==  Sends stop NetCOPE control transaction to HW
    // ========================================================================
    task sendStop();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.data    = new[8];
      
      // NetCOPE header
      controlTrans.data[0] = 0;  // endpointID
      controlTrans.data[1] = 0;   // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 4;   // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 0;   // ifcProtocol
      controlTrans.data[7] = 0;   // ifcInfo
      
      controlTrans.endpointID  = 0;
      controlTrans.transType   = 4;  // control stop transaction
      controlTrans.ifcProtocol = 1;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("STOP CONTROL");
      pport.put(controlTrans);    // put transaction to mailbox
      this.controlTrs++;
    endtask : sendStop
    
    
    // Sends waitfor control transaction to HW.    
     
    task sendWait(int clocks);
      NetCOPETransaction controlTrans = new();
      logic [63:0] data = clocks;
      
      controlTrans.data = new[16];
      
      // NetCOPE header
      controlTrans.data[0] = 0;  // endpointID
      controlTrans.data[1] = 0;   // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 2;   // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 0;   // ifcProtocol
      controlTrans.data[7] = 0;   // ifcInfo
      
      controlTrans.endpointID  = 0;
      controlTrans.transType   = 2;  // control wait transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      for(int i=0; i<8; i++)
        for(int j=0; j<8; j++)
          controlTrans.data[i+8][j] = data[i*8+j];
      
      //controlTrans.display("WAIT FOR CONTROL");
      pport.put(controlTrans);    // put transaction to mailbox  
    endtask : sendWait
    
    // Sends waitforever control transaction to HW.    
    task sendWaitForever();
      NetCOPETransaction controlTrans = new();
      
      controlTrans.data = new[8];
      
      // NetCOPE header
      controlTrans.data[0] = 0;  // endpointID
      controlTrans.data[1] = 0;   // endpointProtocol
      controlTrans.data[2] = 0; 
      controlTrans.data[3] = 0;
      controlTrans.data[4] = 3;   // transType
      controlTrans.data[5] = 0;
      controlTrans.data[6] = 0;   // ifcProtocol
      controlTrans.data[7] = 0;   // ifcInfo
      
      controlTrans.endpointID  = 0;
      controlTrans.transType   = 3;  // control wait transaction
      controlTrans.ifcProtocol = 0;  // no protocol
      controlTrans.ifcInfo     = 0;  // no info
      
      //controlTrans.display("WAIT FOREVER CONTROL");
      pport.put(controlTrans);    // put transaction to mailbox
    endtask : sendWaitForever

 endclass : Sender
