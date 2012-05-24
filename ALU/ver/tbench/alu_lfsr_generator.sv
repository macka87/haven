/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    Transaction LFSR Generator Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         24.5.2012 
 * ************************************************************************** */

 class AluLFSRGenerator #(pDataWidth = 8) extends Generator;
  
   /*
    * Public Class Atributes
    */
 
   LFSR #(4) opGen;               //! LFSR generator for operation
   
   mailbox #(logic [3:0]) opMbx;  //! Mailbox for generated values
    
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
    function new(string inst, 
                 int gen_output = 0, 
                 int stream_id = -1, 
                 tTransMbx transMbx = null
                 );      
      
      logic [3:0][3:0] opSeed;
      
      super.new(inst, gen_output, stream_id, transMbx);
      
      opMbx  = new(1);
      opSeed = {4'1101, 4'1110, 4'1111, 4'0111};
      
      //! Create generators
      opGen = new("OPERATION Generator", opMbx, opSeed, 4'0011);
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
            trans_file = $fopen("trans_file.txt", "w");
            $fwrite(trans_file, "%d\n", stop_after_n_insts);
          end  
          else if (gen_output == 2) 
            trans_file = $fopen("trans_file.txt", "r"); 
          
          opGen.setEnabled();   
          
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
      opGen.setDisabled();  
    endtask : setDisabled
    
   /*
    * Run task.
    */    
    virtual task run();
      Transaction trans;
      logic [3:0] op; 
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
          
          // Set random values according to LFSR
          opMbx.get(op);
          $write("operation: %b\n", op);
          trans.operation = op;
          
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
  endclass : AluLFSRGenerator

