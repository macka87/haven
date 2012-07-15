/* *****************************************************************************
 * Project Name: HAVEN
 * File Name:    FrameLink Coverage Reporter Class
 * Description: 
 * Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
 * Date:         14.7.2012 
 * ************************************************************************** */
 
 class FrameLinkCoverageReporter extends CoverageReporter;

   logic[23:0] coverage_bitmap; // bitmap in SW
   int num_of_coverpoints;      // number of coverpoints
   int covered;                 // number of covered coverpoints

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
       
       this.coverage_bitmap    = 0;
       this.num_of_coverpoints = 17;
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
      logic[23:0] rec_coverage_bitmap = 0;  // bitmap from HW 
      
      while (enabled) begin 
        // receive data from mailbox
        busy  = 0;
        mbx.get(tr);
        busy  = 1;
        
        $cast(ntr, tr);
        //ntr.display("COVERAGE REPORTER:");
        
        // coverage information for FrameLink
     
      /*  
      | 0.bit | 1.bit | 2.bit | 3.bit | 4.bit | 5.bit | 6.bit | 7.bit |
      | SOF_N | SOF_N | SOF_N | SOP_N | EOP_N | SOP_N | SOP_N | EOP_N |
      | SOP_N | SOP_N | SOP_N | EOP_N | EOF_N | EOP_N |
      | EOF_N | EOP_N |       | EOF_N |
      | EOP_N |
        
      | 8.bit  | 9.bit | 10.bit | 11.bit | 12.bit | 13.bit | 14.bit | 15.bit |
      | ~SOF_N | 
      | ~SOP_N | 
      | ~EOF_N | 
      | ~EOP_N |
        
      | 16.bit | 17.bit | 18.bit | 19.bit | 20.bit | 21.bit | 22.bit | 23.bit |
      | REM 0  | REM 1  | REM 2  | REM 3  | REM 4  | REM 5  | REM 6  | REM 7  |       
      */

        // measured coverage info from hardware
        for (int i=0; i<3; i++) 
          for (int j=0; j<8; j++)
            rec_coverage_bitmap[i*8 + j] = ntr.data[8+i][j];
            
        $write("rec_coverage_bitmap %x\n", rec_coverage_bitmap);     
        
        // update SW coverage bitmap
        coverage_bitmap = coverage_bitmap | rec_coverage_bitmap;
        
        $write("coverage_bitmap %x\n", coverage_bitmap);    
        
        // count number of covered coverpoints
        covered = 0;
        for (int i=0; i<24; i++) 
          if (coverage_bitmap[i]) covered++;
          
      end
    endtask : run
    
   /*! 
    * Display coverage statistic.
    */ 
    virtual task display();
      real coverage = (real'(covered))/num_of_coverpoints * 100;
    
      $write("-------------------------------------------------------------\n");
      $write("-- COVERAGE STATISTICS:\n");
      $write("-------------------------------------------------------------\n");
      $write("Coverage for RX FrameLink Interface: %.2f percent\n",
              coverage);
      $write("-------------------------------------------------------------\n");
    endtask
   
 endclass : FrameLinkCoverageReporter
