/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Transaction Generator Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         25.6.2012 
 * ************************************************************************** */

 class Generator;
  
   /*
    * Public Class Atributes
    */
 
   /*!
    * Internal mailbox is used only when no mailbox is specified in the
    * constructor.
    */
    tTransMbx transMbx;
    
   /*!
    * Mailbox for transactions generated in harwdare.
    */ 
    tTransMbx hwTransMbx;
    
    int input_file;        // input file with transactions
    int output_file;       // output file with transactions
    
   /*
    * GENERATOR INPUT.
    *
    * Enumeration type for inputs of Generator:
    * SV_GEN      = SystemVerilog generator of transactions
    * EXT_FILE_IN = reading transactions from external file  
    * OTHER_GEN   = other generator of transactions
    * HW_GEN      = hardware generator of transactions 
    */
    tGenInput gen_input = SV_GEN;
    
   /*
    * GENERATOR OUTPUT.
    *
    * Enumeration type for storage outputs of Generator
    * SV_SIM          = SystemVerilog simulation
    * EXT_FILE_OUT    = storing transactions into external file
    * SV_SIM_EXT_FILE = SystemVerilog simulation and storing to ext. file
    */
    tGenOutput gen_output = SV_SIM;

   /*!
    * The generator will stop after the specified number of object
    * instances has been generated and consumed by the output channel.
    * The generator must be reset before it can be restarted. If the
    * value of this property is 0, the generator will not stop on
    * its own.
    */
    int unsigned stop_after_n_insts = 0;
    
   /*
    * Transaction or data descriptor instance that is repeatedly
    * randomized to create the random content of the output descriptor
    * stream. The individual instances of the output stream are copied
    * from this instance, after randomization, using the Transaction::copy()
    * method. Data_id property of this instance is also set before each 
    * randomization. It will be reset to 0 when the generator is reset and 
    * after the specified maximum number of instances has been generated.
    */
    Transaction blueprint;
    bit         enabled;    //! Generator is enabled
    string      inst;       //! Generator identification 

   /*
    * Protected Class Atributes
    */
    protected int data_id;
    
   /*
    * Public Class Methods
    */
    
   /*!
    * Creates a new instance of the generator class with the specified
    * instance name and optional stream identifier. The generator can
    * be optionally connected to the specified output channel(mailbox).
    * If no output channel instance is specified, one will be created
    * internally in the out_chan property.
    * 
    * \param inst - generator instance name
    * \param transMbx - mailbox for generated transactions
    * \param hwTransMbx - mailbox for transactions from hardware generator                   
    */
    function new(string inst, 
                 tGenInput gen_input = SV_GEN,
                 tGenOutput gen_output = SV_SIM,
                 int stream_id = -1,
                 tTransMbx transMbx = null,
                 tTransMbx hwTransMbx = null
                 );      
      if (transMbx == null) 
        this.transMbx = new(1);
      else 
        this.transMbx = transMbx;


      this.hwTransMbx = hwTransMbx;
      this.gen_input  = gen_input;       // Source of transactions' flow
      this.gen_output = gen_output;      // Destination of transactions' flow
      enabled         = 0;               // Disable generator by default
      blueprint       = null;            // Null the blueprint transaction
      data_id         = 0;               // Set default data identifier
    endfunction : new
    
   /*!
    * Enable generator for creating n Instances.
    */
    task setEnabled(int unsigned nInst=32'hFFFFFFFF);
      enabled = 1;
      stop_after_n_insts = nInst;
      data_id = 0;
      if ( blueprint != null) 
        fork
          //! open input file with transactions
          if (gen_input == EXT_FILE_IN) begin
            input_file = $fopen("trans_input.txt", "r");
            if (input_file == 0) begin
              $write("Input file corrupted!!!");
              $stop;
            end  
          end
          
          //! run configuration for hw generator
          if (gen_input == HW_GEN) 
            blueprint.configureRegisters(stop_after_n_insts);
                    
          //! open output file where transactions will be written
          if (gen_output == EXT_FILE_OUT || gen_output == SV_SIM_EXT_FILE) begin
            output_file = $fopen("trans_output.txt", "w");
            if (output_file == 0) begin
              $write("Output file corrupted!!!");
              $stop;
            end
            $fwrite(output_file, "%d\n", stop_after_n_insts);
          end  
          
          //! run generator
          run();
        join_none
      else
        $write("The blueprint transaction in generator must be set\n");
    endtask : setEnabled
    
   /*
    * Disable generator immediately.
    */
    task setDisabled();
      this.enabled = 0;
      //! close input file with transactions
      if (gen_input == EXT_FILE_IN) 
        $fclose(input_file);
      
      //! close output file where transactions were written
      if (gen_output == EXT_FILE_OUT || gen_output == SV_SIM_EXT_FILE) 
        $fclose(output_file);  
    endtask : setDisabled
    
   /*
    * Run task.
    */    
    virtual task run();
      Transaction trans;
      int trCount, r;
      int counter = 0;
      
      //! ---------------------- SystemVerilog Generator -----------------------
      if (gen_input == SV_GEN) begin
        while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin       
          trans = blueprint.copy;      //! Copy from blueprint
          trans.data_id = data_id;     //! Set instance count
          assert(trans.randomize);     //! Randomize transaction
          //trans.display(inst);       //! Display transaction
      
          //! Output flow of transactions 
          priority case (gen_output)
            //! SV mailbox 
            SV_GEN : transMbx.put(trans);         //! Put transactions into SV mailbox 
            //! External file 
            EXT_FILE_OUT : trans.fwrite(output_file); //! Put transactions into external file
            //! SV mailbox and external file
            SV_SIM_EXT_FILE : begin
                  transMbx.put(trans);       //! Put transactions into SV mailbox
                  trans.fwrite(output_file); //! Put transactions into external file
                end
          endcase
          
          data_id = data_id+1;         //! Increment instance counter      
        end
      end          
      
      //! ------------ Reading of transactions from external file --------------
      if (gen_input == EXT_FILE_IN) begin
        
        //! Preprocessing of external file
        r = $fscanf(input_file,"%d\n", trCount);
        if (r==0) begin
          $write("File corrupted!!!");
          $stop;
        end 
        
        if (trCount < stop_after_n_insts) begin
          $write("Not enough transactions in data file!!!");
          $stop;
        end 
        
        while (enabled && !$feof(input_file) && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin
          trans = blueprint.copy;    //! Copy from blueprint
          trans.data_id = data_id;   //! Set instance count
          trans.fread(input_file);   //! Get transaction from external file
          //trans.display(inst);
          
          //! Output flow of transactions 
          priority case (gen_output)
            //! SV mailbox 
            SV_SIM : transMbx.put(trans);    //! Put transactions into SV mailbox 
            //! External file 
            EXT_FILE_OUT : trans.fwrite(output_file); //! Put transactions into external file
            //! SV mailbox and external file
            SV_SIM_EXT_FILE : begin
                  transMbx.put(trans);       //! Put transactions into SV mailbox
                  trans.fwrite(output_file); //! Put transactions into external file
                end
          endcase
          
          data_id = data_id+1; 
        end
      end  
        
      //! ------------ Other generator - not supported yet ---------------------
      if (gen_input == OTHER_GEN) begin  
        $write("Other input generator than SystemVerilog not supported yet!!!");
        $stop;
      end 
      
      //! -------------------- Hadware generator -------------------------------
      if (gen_input == HW_GEN) begin  
        while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin       
          hwTransMbx.get(trans);       //! Get transaction from mailbox
          trans.data_id = data_id;     //! Set instance count
          //trans.display("GENERATOR (from HW)");         //! Display transaction
      
          //! Output flow of transactions 
          priority case (gen_output)
            //! SV mailbox 
            SV_SIM : transMbx.put(trans); //! Put transactions into SV mailbox 
            //! External file 
            EXT_FILE_OUT : trans.fwrite(output_file); //! Put transactions into external file
            //! SV mailbox and external file
            SV_SIM_EXT_FILE : begin
                  transMbx.put(trans);       //! Put transactions into SV mailbox
                  trans.fwrite(output_file); //! Put transactions into external file
                end
          endcase
          
          data_id = data_id+1;         //! Increment instance counter      
        end
      end   
          
      enabled = 0;  
    endtask : run
  endclass : Generator
