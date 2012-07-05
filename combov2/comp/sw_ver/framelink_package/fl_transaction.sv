/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    fl_transaction
 * Description:  FrameLink Transaction Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

 import dpi_mi32_wrapper_pkg::*; 

 class FrameLinkTransaction extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
   //! --- RANDOMIZATION OF TRANSACTION PARAMETERS ---
   
    int dataWidth       = 4;            //! data width in Bytes 
    
    int frameParts      = 3;            //! Count of FrameLink frame parts  
    int partSizeMax[]   = '{32,32,32};  //! Maximal size of FrameLink frame part
    int partSizeMin[]   = '{8,8,8};     //! Minimal size of FrameLink frame part
    
   //! Randomized transaction data [packet][byte]
    rand byte unsigned data[][];

   //! Transaction data constraint
    constraint c1 {
      data.size == frameParts;
            
      foreach (data[i]) 
        data[i].size inside {
                             [partSizeMin[i]:partSizeMax[i]]
                            };
    };
    
   //! --- RANDOMIZATION OF DELAY PARAMETERS ---
   
   //! Enable/Disable delays "between transactions" according to weights
    rand bit enBtDelay;   
         byte btDelayEn_wt  = 1; 
         byte btDelayDi_wt  = 3;

    //! Value of delay "between transactions" randomized inside boundaries
    rand byte btDelay; 
         byte btDelayLow    = 0;
         byte btDelayHigh   = 3;
    
    //! Enable/Disable delays "inside transaction" according to weights 
    rand bit enItDelay;     
         byte itDelayEn_wt  = 1; 
         byte itDelayDi_wt  = 3;
    
    //! Value of delay "inside transaction" randomized inside boundaries  
    rand byte itDelay[][];  
         byte itDelayLow    = 0;
         byte itDelayHigh   = 3;
    
    //! Constraints for randomized values 
    constraint cDelay1 {
      enBtDelay dist { 1'b1 := btDelayEn_wt,
                       1'b0 := btDelayDi_wt
                     };
    };                 

    constraint cDelay2 {
      btDelay inside {
                      [btDelayLow:btDelayHigh]
                     };
    };                 

    constraint cDelay3 {
      enItDelay dist { 1'b1 := itDelayEn_wt,
                       1'b0 := itDelayDi_wt
                     };
    };                 
     
    constraint cDelay4 {    
      itDelay.size == frameParts;
      
      foreach (itDelay[i])
        itDelay[i].size == partSizeMax[i]/dataWidth + 1;
                 
      foreach (itDelay[i,j])
        itDelay[i][j] inside {
                              [itDelayLow:itDelayHigh]
                             };               
    }; 
   
   /*
    * Public Class Methods
    */
    
   /*!
    * Function displays the current value of the transaction or data described
    * by this instance in a human-readable format on the standard output.
    *
    * \param prefix - transaction type
    */
    virtual function void display(string prefix = "");
      if (prefix != "") begin
        $write("---------------------------------------------------------\n");
        $write("-- %s\n",prefix);
        $write("---------------------------------------------------------\n");
      end
      
      $write("datawidth in bytes : %d\n",dataWidth);
      $write("frameParts : %d\n",frameParts);
       
      $write("TRANSACTION PARAMETERS: \n");
      for (integer i=0; i < frameParts; i++) begin
        $write("Part no: %1d, Part size: %1d, Data:", i, data[i].size);
        
        for (integer j=0; j < data[i].size; j++) begin 
          if (j%16==0) $write("\n%4x:",j);
          if (j%8==0) $write(" ");
          $write("%x ",data[i][j]);
        end  
        $write("\n");
      end  
      $write("\n");  
      
      $write("DELAY PARAMETERS: \n");
      $write("enBtDelay: %x\n",enBtDelay);
      $write("btDelay: %x\n",btDelay);
      $write("enItDelay: %x\n",enItDelay);
      
      for (int i=0; i < frameParts; i++) begin
        $write("itDelay part: %d\n",i);
        for (int j=0; j < itDelay[i].size; j++)                                            
          $write("%x ",itDelay[i][j]);
        $write("\n");
      end
      $write("\n");    
    endfunction : display
 
   /*!
    * Copies the current value of the object instance to the specified object
    * instance. Returns a reference to the target instance.
    * 
    * \param to - original transaction        
    */
    virtual function Transaction copy(Transaction to = null);
      FrameLinkTransaction tr;
      if (to == null)
        tr = new();
      else 
        $cast(tr, to);
      
      tr.dataWidth     = dataWidth;
      tr.frameParts    = frameParts;
      tr.partSizeMax   = new[frameParts];
      tr.partSizeMin   = new[frameParts];
      tr.data          = new[frameParts];
      for (int i=0; i < frameParts; i++)
        tr.data[i]     = new[data[i].size];

      tr.partSizeMax   = partSizeMax;
      tr.partSizeMin   = partSizeMin;
      tr.data          = data;
      
      tr.btDelayEn_wt  = btDelayEn_wt;
      tr.btDelayDi_wt  = btDelayDi_wt;
      tr.btDelayLow    = btDelayLow;
      tr.btDelayHigh   = btDelayHigh;

      tr.itDelayEn_wt  = itDelayEn_wt;
      tr.itDelayDi_wt  = itDelayDi_wt;
      tr.itDelayLow    = itDelayLow;
      tr.itDelayHigh   = itDelayHigh;

      tr.enBtDelay     = enBtDelay;   
      tr.btDelay       = btDelay; 
      tr.enItDelay     = enItDelay;     
      tr.itDelay       = new[frameParts];  
      for (int i=0; i < frameParts; i++)
        tr.itDelay[i]  = new[itDelay[i].size];
      tr.itDelay       = itDelay;
         
      copy = tr;
    endfunction: copy
       
 	 /*!
    * Compares the current value of the object instance with the current value
    * of the specified object instance, according to the specified kind. Returns
    * TRUE (i.e., non-zero) if the value is identical. If the value is 
    * different, FALSE is returned and a descriptive text of the first
    * difference found is returned in the specified string variable. The kind 
    * argument may be used to implement different comparison functions (e.g.,
    * full compare, comparison of rand properties only, comparison of all 
    * properties physically implemented in a protocol and so on.)
    * 
    * \param to - transaction instance
    * \param diff - first difference
    * \param kind - comparation function                 
    */
    virtual function bit compare(input Transaction to, 
                                 output string diff, input int kind = -1);
      bit same = 1; 
      FrameLinkTransaction tr;
      $cast(tr, to);
       
      if (frameParts != tr.frameParts) begin 
        same = 0;
        $swrite(diff, "count of frameParts does not match");
      end
       
      for (integer i=0; i<frameParts; i++) begin
        if (data[i].size != tr.data[i].size) begin
          same = 0;
          $swrite(diff, "partSize[%0d] does not match", i);
        end
      end
       
      for (integer i=0; i < frameParts; i++)   
        for (integer j=0; j < data[i].size; j++)
          if (data[i][j] != tr.data[i][j]) begin 
            same = 0;
            $swrite(diff, "data[%0d][%0d] does not match", i, j);
          end
           
      compare = same;
    endfunction: compare 
    
   /*!
    * Configuration of hardware registers according to constraints in FrameLink
    * transaction. They are applied in hardware generator in hardware version
    * of verification environment.        
    */   
    function void configureRegisters(int transCount);
      logic [31:0] hw_addr_gen        = 32'h01100000;   // hw addr for generator
      logic [31:0] hw_addr_adapt      = 32'h01101000;   // hw addr for adapter
      logic [31:0] gen_seed           = 32'h00000004;
      logic [31:0] run_reg_addr       = 32'h00000000;
      logic [31:0] trans_reg_addr     = 32'h00000004;
      logic [31:0] part_num_reg_addr  = 32'h00000010;
      logic [31:0] part_size_reg_addr = 32'h00000080;
      logic [31:0] part_mask_offset   = 32'h00000000;
      logic [31:0] part_base_offset   = 32'h00000004;
      logic [31:0] part_max_offset    = 32'h00000008;
      logic [31:0] part_reg_offset    = 32'h00000010;
      
      logic [31:0] frame_parts        = frameParts;
      logic [31:0] data;
      
      logic [31:0] part_size_min[]      = new[frameParts];
      logic [31:0] part_size_max[]      = new[frameParts];
      
      for (int i=0; i<frameParts; i++) begin
        part_size_min[i] = partSizeMin[i];
        part_size_max[i] = partSizeMax[i];
      end  
    
      // part num
      c_writeToRegister(hw_addr_adapt + part_num_reg_addr + part_mask_offset, 32'h00000007);
      c_writeToRegister(hw_addr_adapt + part_num_reg_addr + part_base_offset, frame_parts);
      c_writeToRegister(hw_addr_adapt + part_num_reg_addr + part_max_offset, 32'h00000000);
      
      // max number of parts is 8
      for (int i=0; i<8; i++) begin
        // part i
        c_writeToRegister(
          hw_addr_adapt + part_size_reg_addr + i*part_reg_offset + part_mask_offset, 
          32'h0000001F
        );
        c_writeToRegister(
          hw_addr_adapt + part_size_reg_addr + i*part_reg_offset + part_base_offset, 
          part_size_min[i]
        );
        c_writeToRegister(
          hw_addr_adapt + part_size_reg_addr + i*part_reg_offset + part_max_offset,
          part_size_max[i] - part_size_min[i]
        ); 
      end 
      
      // transaction count
      c_writeToRegister(hw_addr_adapt + trans_reg_addr, transCount);
      
      // set seed of the generator
      c_writeToRegister(hw_addr_gen + gen_seed, 32'h00011ACA);
      
      // run generator
      c_writeToRegister(hw_addr_gen, 32'h00000001);
      
      // run adapter
      c_writeToRegister(hw_addr_adapt + run_reg_addr, 32'h00000001);
    endfunction : configureRegisters
    
   /*!
    * Function for writing transaction into an external file. 
    */
    function void fwrite(int fileDescr);
      
    endfunction : fwrite
    
   /*!
    * Function for reading transaction from an external file. 
    */
    function void fread(int fileDescr);
      
    endfunction : fread 
 endclass: FrameLinkTransaction
                                                                                   