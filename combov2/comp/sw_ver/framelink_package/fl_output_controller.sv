/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Output Controller Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         3.5.2011 
 * ************************************************************************** */
 
 class FrameLinkOutputController extends OutputController;
   
   /*
    * Public Class Atributes
    */ 
    int frameCount;
    int counter;
    
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
       this.counter    = 0;
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
      fltr.frameParts = frameCount; // plus netcope header
      fltr.data  = new[frameCount];
        
      while (enabled) begin 
        // fill FrameLink packet with received data
        for (int i=0; i<frameCount; i++) begin
          
          // ------ receive data from mailbox ------
          busy = 0;
          outputMbx.get(tr);
          busy = 1;
          
          $cast(ntr, tr);
          
          // creates one FrameLink part from received data - NetCOPE Header Size 
          fltr.data[i] = new[ntr.size-8]; 
            
          // jump over NetCOPE header  
          for (int j=0; j<ntr.size-8; j++)
            fltr.data[i][j] = ntr.data[j+8];
            
          // ------ receive control information from mailbox ------   
          busy = 0;
          outputMbx.get(tr);
          busy = 1; 
          
          $cast(ntr, tr);
          
          if (ntr.data[4] == 1) $write("FL_OUT_CNTRL: EOP\n");
          else if (ntr.data[4] == 3) $write("FL_OUT_CNTRL: EOF\n");
          else begin
                 $write("FL_OUT_CNTRL: Unsupported control sequence!!!");
                 $stop;
               end
        end     

        $cast(tr, fltr);
        counter++;
        
        //! Call transaction postprocesing in scoreboard  
        foreach (cbs[i])          
          cbs[i].post_tr(tr, id); 
      end  
    endtask : run
 endclass : FrameLinkOutputController  
