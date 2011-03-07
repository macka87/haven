/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    fl_gen_input_controller
 * Description:  Input Controller of Generated FrameLink Class
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class FrameLinkGenInputController extends GenInputController;
   
   /*
    * Public Class Atributes
    */ 
  
    FrameLinkTransaction flBlueprint;    // Transaction format
    tTransMbx transMbx;                  // Transaction mailbox
    
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
    function new (int frameParts, int partSizeMax[], int partSizeMin[]); 
      // Create mailbox
      this.transMbx = new(0);
      // Create generator
      generator   = new("FrameLink Generator", transMbx);
      // Create blueprint transaction
      flBlueprint = new;
      flBlueprint.frameParts    = frameParts;
      flBlueprint.partSizeMax   = partSizeMax;
      flBlueprint.partSizeMin   = partSizeMin;
      generator.blueprint       = flBlueprint;
    endfunction: new  
    
   /*!
    * Send generated transaction 
    */
    task sendGenerated(int unsigned transCount);
       // run generator
       $write("bude sa volat generator\n");
       generator.setEnabled(transCount);
    endtask : sendGenerated 
   
 endclass : FrameLinkGenInputController
  