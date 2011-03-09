/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    fl_transaction
 * Description:  FrameLink Transaction Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */

 class FrameLinkTransaction extends Transaction;
      
   /*
    * Public Class Atributes
    */
   
   //! Randomization transaction parameters
    int frameParts     = 3;            //! Count of FrameLink frame parts  
    int partSizeMax[]  = '{32,32,32};  //! Maximal size of FrameLink frame part
    int partSizeMin[]  = '{8,8,8};     //! Minimal size of FrameLink frame part
    int totalWords     = 0;
    int dataWidth      = 32;
   
   //! Randomized transaction data [packet][byte]
    rand byte unsigned data[][];

   //! Transaction data constraint
    constraint c1 {
      data.size == frameParts;
      
      foreach (data[i]) 
        data[i].size inside {
                             [partSizeMin[i]:partSizeMax[i]]
                            };
      foreach (data[i]) 
        if (data[i].size % dataWidth == 0) 
          totalWords == totalWords + data[i].size/dataWidth;
        else   
          totalWords == totalWords + data[i].size/dataWidth + 1; 
    };
    
   //! Enable/Disable delays "between transactions" according to weights
    rand bit enBtDelay;   
         int btDelayEn_wt  = 1; 
         int btDelayDi_wt  = 3;

   //! Value of delay "between transactions" randomized inside boundaries
    rand int btDelay; 
         int btDelayLow    = 0;
         int btDelayHigh   = 3;
    
   //! Enable/Disable delays "inside transaction" according to weights 
    rand bit enItDelay;     
         int itDelayEn_wt  = 1; 
         int itDelayDi_wt  = 3;
    
   //! Value of delay "inside transaction" randomized inside boundaries  
    rand int itDelay[];  
         int itDelayLow    = 0;
         int itDelayHigh   = 3;
    
   //! Constraints for randomized values 
    constraint cDelay1{
      enBtDelay dist { 1'b1 := btDelayEn_wt,
                       1'b0 := btDelayDi_wt
                     };
    };                 
    
    constraint cDelay2{
      btDelay inside {
                      [btDelayLow:btDelayHigh]
                     };
    };
    
    constraint cDelay3{
      enItDelay dist { 1'b1 := itDelayEn_wt,
                       1'b0 := itDelayDi_wt
                     };
    };
    
    constraint cDelay4{   
      itDelay.size == totalWords;             
      
      foreach (itDelay[i])
        itDelay[i] inside {
                           [itDelayLow:itDelayHigh]
                          };               
    };
    
   /*
    * Public Class Methods
    */
    
   /*!
    * Constructor - creates transaction object 
    */           
    function new (int dataWidth); 
      this.dataWidth = dataWidth;
    endfunction: new 
  
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
        tr = new(dataWidth);
      else 
        $cast(tr, to);

      tr.frameParts    = frameParts;
      tr.partSizeMax   = new[frameParts];
      tr.partSizeMin   = new[frameParts];
      tr.data          = new[frameParts];
      for (integer i=0; i < frameParts; i++)
        tr.data[i]     = new[data[i].size];

      tr.partSizeMax   = partSizeMax;
      tr.partSizeMin   = partSizeMin;
      tr.data          = data;
       
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
 endclass: FrameLinkTransaction
