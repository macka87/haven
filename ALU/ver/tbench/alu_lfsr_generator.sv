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
 
   LFSRSimple #(4) opGen;        //! LFSR generator for operation
   LFSRSimple #(8) opAGen;       //! LFSR generator for operandA
   LFSRSimple #(8) opBGen;       //! LFSR generator for operandB
   LFSRSimple #(8) opIMMGen;     //! LFSR generator for operandIMM
   LFSRSimple #(8) opMEMGen;     //! LFSR generator for operandMEM
   LFSRSimple #(2) moviGen;      //! LFSR generator for movi
   
   //! Mailboxes for generated values
   mailbox #(logic [3:0]) opMbx; 
   mailbox #(logic [7:0]) opAMbx; 
   mailbox #(logic [7:0]) opBMbx; 
   mailbox #(logic [7:0]) opIMMMbx; 
   mailbox #(logic [7:0]) opMEMMbx; 
   mailbox #(logic [1:0]) moviMbx; 
    
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
                 int gen_input = 0,
                 int gen_output = 0,
                 int stream_id = -1,
                 tTransMbx transMbx = null
                 );      
      
      logic [3:0] opSeed;
      logic [3:0] opPolynomial;
      
      logic [3:0] opASeed;
      logic [3:0] opBSeed;
      logic [3:0] opIMMSeed;
      logic [3:0] opMEMSeed;
      logic [3:0] operandsPolynomial;
      
      logic [3:0] moviSeed;
      logic [3:0] moviPolynomial;
      
      super.new(inst, gen_input, gen_output, stream_id, transMbx);
      
      opMbx     = new(1);
      opAMbx    = new(1);
      opBMbx    = new(1);
      opIMMMbx  = new(1);
      opMEMMbx  = new(1);
      moviMbx   = new(1);
      
      opSeed = 4'b1111;
      opPolynomial = 4'b1100; // x^4 + x^3 + 1   [1100]1
      
      opASeed   = 8'b11110000;
      opBSeed   = 8'b11111000;
      opIMMSeed = 8'b01011111;
      opMEMSeed = 8'b10101111;
      operandsPolynomial = 8'b10111000; // x^8 + x^6 + x^5 + x^4 + 1   [10111000]1
      
      moviSeed = 2'b11;
      moviPolynomial = 2'b11; // x^2 + x^1 + 1   [11]1
      
      //! Create generators
      opGen    = new("OPERATION Generator", opMbx, opSeed, opPolynomial);
      opAGen   = new("OPERAND A Generator", opAMbx, opASeed, operandsPolynomial);
      opBGen   = new("OPERAND B Generator", opBMbx, opBSeed, operandsPolynomial);;       
      opIMMGen = new("OPERAND IMM Generator", opIMMMbx, opIMMSeed, operandsPolynomial);;     
      opMEMGen = new("OPERAND MEM Generator", opMEMMbx, opMEMSeed, operandsPolynomial);;     
      moviGen  = new("MOVI Generator", moviMbx, moviSeed, moviPolynomial);;      
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
          opAGen.setEnabled();  
          opBGen.setEnabled();  
          opIMMGen.setEnabled();  
          opMEMGen.setEnabled();  
          moviGen.setEnabled();   
          
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
      opAGen.setDisabled();  
      opBGen.setDisabled();  
      opIMMGen.setDisabled();  
      opMEMGen.setDisabled();  
      moviGen.setDisabled(); 
    endtask : setDisabled
    
   /*
    * Run task.
    */    
    virtual task run();
      Transaction trans;
      ALUInTransaction #(pDataWidth) tr;
      logic [3:0] op; 
      logic [7:0] opA; 
      logic [7:0] opB; 
      logic [7:0] opIMM; 
      logic [7:0] opMEM; 
      logic [1:0] movi; 
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
          opAMbx.get(opA);
          opBMbx.get(opB);
          opIMMMbx.get(opIMM);
          opMEMMbx.get(opMEM);
          
          // MOVI constraint
          do
           moviMbx.get(movi);
          while (movi == 2'b11);
          
          $cast(tr, trans);
          
          tr.operation  = op;
          tr.operandA   = opA;
          tr.operandB   = opB;
          tr.operandIMM = opIMM;
          tr.operandMEM = opMEM;
          tr.movi       = movi;
          
          trans.display(inst);         //! Display transaction
        
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

