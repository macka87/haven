/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    fl_gen_input_controller
 * Description:  Input Controller of Generated FrameLink Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class FrameLinkGenInputController #(int pDataWidth=32)
       extends GenInputController;
   
   /*
    * Public Class Atributes
    */ 
  
    FrameLinkTransaction flBlueprint;  //! Transaction format
       
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    * 
    * \param frameParts  - count of FrameLink frame parts
    * \param partSizeMax - maximal size of FrameLink frame part        
    * \param partSizeMin - minimal size of FrameLink frame part    
    */    
    function new (int framework, 
                  int frameParts, int partSizeMax[], int partSizeMin[],
                  int btDelayEn_wt, int btDelayDi_wt, 
                  int btDelayLow, int btDelayHigh,
                  int itDelayEn_wt, int itDelayDi_wt, 
                  int itDelayLow, int itDelayHigh
                 ); 
                 
      super.new(framework);
      
      // Create generator
      generator      = new("FrameLink Generator", transMbx);
      
      // Create blueprint transaction
      $write("datawidth in controler: %d\n",pDataWidth);
      flBlueprint    = new();
      
      flBlueprint.dataWidth     = pDataWidth/8;
      
      flBlueprint.frameParts    = frameParts;
      flBlueprint.partSizeMax   = partSizeMax;
      flBlueprint.partSizeMin   = partSizeMin;
      
      flBlueprint.btDelayEn_wt  = btDelayEn_wt;
      flBlueprint.btDelayDi_wt  = btDelayDi_wt;
      flBlueprint.btDelayLow    = btDelayLow;
      flBlueprint.btDelayHigh   = btDelayHigh;
            
      flBlueprint.itDelayEn_wt  = itDelayEn_wt;
      flBlueprint.itDelayDi_wt  = itDelayDi_wt;
      flBlueprint.itDelayLow    = itDelayLow;
      flBlueprint.itDelayHigh   = itDelayHigh;
            
      generator.blueprint       = flBlueprint;
    endfunction: new  
    
   /*!
    * Send generated transaction 
    */
    task sendGenerated(int unsigned transCount);
       // run generator
       generator.setEnabled(transCount);
    endtask : sendGenerated 
   
 endclass : FrameLinkGenInputController
  