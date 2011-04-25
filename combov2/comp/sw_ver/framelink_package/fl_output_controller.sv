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
    int frameCount;
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx outputMbx, 
                 int frameCount); 
       super.new(inst, id, outputMbx);
       this.frameCount = frameCount;
    endfunction: new
    
   /*! 
    * Run Controller - receives transactions and sends them for processing by 
    * callback.
    */ 
    task run();
      NetCOPETransaction ntr;
      FrameLinkTransaction fltr;
      Transaction tr;

      // create new FrameLink packet
      fltr = new();
      fltr.frameParts = frameCount;
      fltr.data  = new[frameCount];
        
      while (enabled) begin 
        // fill FrameLink packet with received data
        for (int i=0; i<frameCount; i++) begin
          // receive data from mailbox
          busy = 0;
          outputMbx.get(tr);
          busy = 1;
          
          $cast(ntr, tr);
          
          // creates one FrameLink part from received data 
          fltr.data[i] = new[ntr.size];
            
          for (int j=0; j<ntr.size; j++)
            fltr.data[i][j] = ntr.data[j];
        end     

        //fltr.display("CREATED OUTPUT FRAMELINK");
          
        $cast(tr, fltr);
          
        //! Call transaction postprocesing in scoreboard  
        foreach (cbs[i])          
          cbs[i].post_tr(tr, id); 
      end
    endtask : run
 endclass : FrameLinkOutputController  
