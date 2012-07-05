/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Generator Output Controller Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         3.7.2012 
 * ************************************************************************** */
 
 class FrameLinkGenOutputController #(int pDataWidth = 64) extends OutputController;
   
   /*
    * Public Class Atributes
    */ 
    int frameCount;     // Number of FrameLink frames
    tTransMbx genMbx;   // Mailbox for transactions generated in hardware 
    
   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx outputMbx,
                 tTransMbx genMbx, 
                 int frameCount); 
       super.new(inst, id, outputMbx);
       this.frameCount = frameCount;
       this.genMbx     = genMbx; 
    endfunction: new
   
   /*! 
    * Run Controller - receives transactions and sends them for processing by 
    * callback.
    */ 
    task run();
      NetCOPETransaction ntr;
      FrameLinkTransaction fltr;
      Transaction tr;
      int numOfWords;

      while (enabled) begin
        // create new FrameLink packet
        fltr = new();
        fltr.frameParts = frameCount; // plus netcope header
        fltr.dataWidth  = pDataWidth/8;
        fltr.data       = new[frameCount];
        fltr.itDelay    = new[frameCount];               
 
        // fill FrameLink packet with received data
        for (int i=0; i<frameCount; i++) begin
          // ----------- receive data from mailbox -----------
          busy = 0;
          outputMbx.get(tr);
          busy = 1;
          
          $cast(ntr, tr);
          
          // check if data arrived
          if (ntr.data[4] != 0) begin
            $write("FL_GEN_OUTPUT CONTROLER : DATA EXPECTED!!!\n"); 
            $stop();
          end  
          
          // creates one FrameLink part from received data - NetCOPE Header Size 
          fltr.data[i] = new[ntr.size-8]; 
          //$write("[ntr.size-8] %d\n", ntr.size-8);
          
          // process inside transactions delays (according to number of words)
          numOfWords = (ntr.size-8)/(pDataWidth/8) + 1;
          //$write("numOfWords %d\n", numOfWords);
          
          // jump over NetCOPE header  
          for (int j=0; j<ntr.size-8; j++)
            fltr.data[i][j] = ntr.data[j+8];
            
          // ----------- receive delay from mailbox -----------  
          busy = 0;
          outputMbx.get(tr);
          busy = 1;
          
          $cast(ntr, tr);
          
          // check if data arrived
          if (ntr.data[4] != 5) begin
            $write("FL_GEN_OUTPUT CONTROLER : DELAY EXPECTED!!!\n"); 
            $stop();
          end 
          
          // process between transactions delays
          fltr.enBtDelay = 1; 
          fltr.btDelay   = ntr.data[8]; 
          
          fltr.enItDelay  = 1; 
          fltr.itDelay[i] = new[numOfWords];
          
          for (int j=0; j<numOfWords; j++)
            fltr.itDelay[i][j] = ntr.data[j+9]; 
        end     

        //fltr.display("OUTPUT FRAMELINK TRANSACTION");

        $cast(tr, fltr);
        
        genMbx.put(tr);
      end  
    endtask : run
 endclass : FrameLinkGenOutputController  
