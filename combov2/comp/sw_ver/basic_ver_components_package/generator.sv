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
    function new(string inst, tTransMbx transMbx = null);
      if (transMbx == null)  
        this.transMbx = new(1);          //! Create own mailbox
      else
        this.transMbx = transMbx;        //! Use created mailbox
    
      enabled         = 0;               //! Disable generator by default
      this.inst       = inst;            //! Store generator identifier
      blueprint       = null;            //! Null the blueprint transaction
      data_id         = 0;               //! Set default data identifier
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
    endtask : setDisabled
    
   /*
    * Run task.
    */    
    virtual task run();
      Transaction trans;
      int counter = 0;
      while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin          
        if (data_id % 4000 == 0) begin
          $write("Generated       %d new blueprint transactions at ", data_id);
          $system("date");
        end
        trans = blueprint.copy;   //! Copy from blueprint
        trans.data_id = data_id;  //! Set instance count
        assert(trans.randomize);  //! Randomize transaction
        //trans.display(inst);      //! Display transaction
        transMbx.put(trans);      //! Put transaction to mailbox
        data_id = data_id+1;      //! Increment instance counter
      end;
      enabled = 0;
    endtask : run
  endclass : Generator
