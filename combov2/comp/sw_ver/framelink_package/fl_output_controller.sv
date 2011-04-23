/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Output Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         27.2.2011 
 * ************************************************************************** */
 
 class FrameLinkOutputController extends OutputController;
   
   /*
    * Public Class Atributes
    */ 
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx outputMbx); 
       super.new(inst, id, outputMbx);
    endfunction: new
    
   /*! 
    * Run Controller - receives transactions and sends them for processing by 
    * callback.
    */ 
    task run();
      Transaction tr;
          
      while (enabled) begin 
        foreach (cbs[i])           //! Call transaction preprocesing
          cbs[i].pre_tr(tr, id);
        
        wait(outputMbx.num()!=0) 
        
        busy = 1;
          
        // receive transaction from output mailbox
        outputMbx.get(tr);

        tr.display("OUTPUT CONTROLLER ZA FIFEM");
        
        foreach (cbs[i])          //! Call transaction postprocesing
          cbs[i].post_tr(tr, id);  
          
        busy = 0;  
      end
    endtask : run
 endclass : FrameLinkOutputController  
