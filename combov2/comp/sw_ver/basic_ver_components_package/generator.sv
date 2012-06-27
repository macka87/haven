/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Transaction Generator Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
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
    int trans_file;
    
    /*
     * It is possible to define the location where transactions are stored.
     * 0 = mailbox
     * 1 = storage to external file 
     * 2 = reading from external file       
     * 3 = mailbox and storage to external file      
     */
    int gen_output = 0;

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
    * \param transMbx - transaction mailbox                
    */
    function new(string inst, int gen_output = 0, int stream_id = -1, tTransMbx transMbx = null);      
      if (transMbx == null) 
        this.transMbx = new(1);
      else 
        this.transMbx = transMbx;

      this.gen_output = gen_output;      // Location of transactions
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
          if (gen_output == 1 || gen_output == 3) begin
            trans_file = $fopen("../atpg/inputs_atpg", "w");
            $fwrite(trans_file, "%d\n", stop_after_n_insts);
          end  
          else if (gen_output == 2) 
            trans_file = $fopen("../atpg/inputs_atpg", "r");  
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
      if (gen_output == 1) $fclose(trans_file);
    endtask : setDisabled
    
   /*
    * Run task.
    */    
    virtual task run();
      Transaction trans;
      int counter = 0;
      
      //! Reading transactions from external file      
      if (gen_output == 2) begin
        int trCount, r;
            
        r = $fscanf(trans_file,"%d\n", trCount);
        if (r==0) begin
          $write("File corrupted!!!");
          $stop;
        end 
        
        if (trCount < stop_after_n_insts) begin
          $write("Not enough transactions in data file!!!");
          $stop;
        end  
        
        while (enabled && !$feof(trans_file) && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin
          trans = blueprint.copy;    //! Copy from blueprint
          trans.data_id = data_id;   //! Set instance count
          trans.fread(trans_file);   //! Get transaction from external file
          trans.display(inst);
          transMbx.put(trans);  
          data_id = data_id+1; 
        end
      end  
        
      else begin 
        while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin          
          trans = blueprint.copy;      //! Copy from blueprint
          trans.data_id = data_id;     //! Set instance count
          assert(trans.randomize);     //! Randomize transaction
          //trans.display(inst);       //! Display transaction
        
          if (gen_output == 0)
            transMbx.put(trans);       //! Put transaction to mailbox
        
          else if (gen_output == 1) 
            trans.fwrite(trans_file);  //! Put transaction to external file
                  
          else if (gen_output == 3) begin
            transMbx.put(trans);
            trans.fwrite(trans_file);  //! Put trans to mailbox and external file
          end
        
          data_id = data_id+1;         //! Increment instance counter
        end;
      end
      
      enabled = 0;  
    endtask : run
  endclass : Generator
