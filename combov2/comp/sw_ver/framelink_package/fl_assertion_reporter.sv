/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    FrameLink Assertion Reporter Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         11.8.2011 
 * ************************************************************************** */
 
 class FrameLinkAssertionReporter extends AssertionReporter;

   /*
    * Public Class Methods
    */ 
    
   /*! 
    * Constructor 
    */    
    function new(string inst,
                 byte id,
                 tTransMbx mbx 
                ); 
       super.new(inst, id, mbx);
    endfunction: new

   /*
    * Private Class Methods
    */ 

   /*! 
    * Run Reporter - receives messages from hardware assertion checker and
    * prints corresponding reports .
    */ 
    virtual task run();
      NetCOPETransaction ntr;
      Transaction tr;
      logic[15:0] assertRep;
      bit error = 0; 

      while (enabled) begin 
        // receive data from mailbox
        busy  = 0;
        error = 0;
        mbx.get(tr);
        busy  = 1;
        
        $cast(ntr, tr);

        // extract assertion message
        assertRep[7:0] = ntr.data[6];
        assertRep[15:8] = ntr.data[7];

        // identify assertion failure
        for (int i=0; i<15; i++)
          if (assertRep[i] == 1) error = 1;

        // !!!!!! it will be necessary to add division between RX and TX reports later,
        // if there will be assertion reporters on both FrameLink interfaces!!!

        // create assertion report
        if (error == 1) begin
          $write("\n");
          $write("!!!!!! Assertion error !!!!!!\n");
          $write("Receiving of %d. transaction failed!\n", ntr.timeStamp);
          $system("date"); 
          $write("\n\n");
          $write("------------ ASSERTION REPORT -----------\n");

          if (assertRep[0]) 
            $write("\nTX FrameLink Assertion Error: SOF_N without SOP_N\n");
        
          if (assertRep[1]) 
            $write("\nTX FrameLink Assertion Error: EOF_N without EOP_N\n");
        
          if (assertRep[2]) 
            $write("\nTX FrameLink Assertion Error: Data between EOP_N and SOP_N\n");
        
          if (assertRep[3]) 
            $write("\nTX FrameLink Assertion Error: Data between EOF_N and SOF_N\n");
        
          if (assertRep[4]) 
            $write("\nTX FrameLink Assertion Error: No EOP_N before SOP_N\n");
          
          if (assertRep[5]) 
            $write("\nTX FrameLink Assertion Error: No EOF_N before SOF_N\n");
          $write("----------------------------------------\n");
          $stop();
        end  
      end
    endtask : run
 endclass : FrameLinkAssertionReporter
