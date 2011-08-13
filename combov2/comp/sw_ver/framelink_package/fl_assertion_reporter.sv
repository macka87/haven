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
      longint timeStamp;
      longint transNum;
      longint checkerId;

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

        checkerId = ntr.data[0];

        timeStamp =
          ntr.data[ 8] + 256 * (ntr.data[ 9] + 256 * (ntr.data[10] + 256 * (
          ntr.data[11] + 256 * (ntr.data[12] + 256 * (ntr.data[13] + 256 * (
          ntr.data[14] + 256 * (ntr.data[15])))))));

        transNum =
          ntr.data[16] + 256 * (ntr.data[17] + 256 * (ntr.data[18] + 256 * (
          ntr.data[19] + 256 * (ntr.data[20] + 256 * (ntr.data[21] + 256 * (
          ntr.data[22] + 256 * (ntr.data[23])))))));

        // !!!!!! it will be necessary to add division between RX and TX reports later,
        // if there will be assertion reporters on both FrameLink interfaces!!!

        // create assertion report
        if (error == 1) begin
          $write("\n");
          $write("!!!!!! Assertion error !!!!!!\n");
          $write("Violation of FrameLink protocol at checker: %d\n", checkerId);
          $write("Clock cycle of violation:                   %d\n", timeStamp);
          $write("Violated transaction #:                     %d\n", transNum);
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
          $write("----------------------------------------\n\n");
          $finish();
        end  
      end
    endtask : run
 endclass : FrameLinkAssertionReporter
