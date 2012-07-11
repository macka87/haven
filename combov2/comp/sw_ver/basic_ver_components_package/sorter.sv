/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification
 * File Name:    Sorter Class
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         10.8.2011 
 * ************************************************************************** */

 class Sorter;

   /*
    * Public Class Atributes
    */ 
    tTransMbx  outputMbx;  //! Output Transaction Mailbox
    tTransMbx  mbx[];      //! Output Controllers' Mailboxes
    int        mbxNum;     //! Number of mailboxes
    bit        enabled;    //! Sorter enabling
    bit        busy;       //! Sorter is receiving transaction
    
   /*
    * Public Class Methods
    */ 
   
   /*! 
    * Constructor 
    */    
    function new(tTransMbx outputMbx,
                 tTransMbx mbx[],
                 int mbxNum); 
      // Create mailbox
      this.outputMbx = outputMbx;
      this.mbx       = mbx;
      this.mbxNum    = mbxNum;
      this.enabled   = 0;         //! Sorter is disabled by default
      this.busy      = 0;         //! Sorter is not busy by default 
    endfunction: new 
    
   /*! 
    * Enable Sorter - enable sorter and runs sorter process
    */    
    virtual task setEnabled();
      enabled = 1;  //! Sorter Enabling
      fork         
         run();     //! Creating sorter subprocess
      join_none;    //! Don't wait for ending
    endtask : setEnabled
        
   /*! 
    * Disable Sorter
    */
    virtual task setDisabled();
      enabled = 0;  //! Disable sorter, after receiving last transaction
    endtask : setDisabled

   /*
    * Private Class Methods
    */
   
   /*! 
    * Run Sorter - receives transactions from output mailbox and 
    * according to NetCOPE header sends them to proper Output controller.
    */      
    virtual task run();
      NetCOPETransaction ntr;
      Transaction tr;
      int monitorID;
      
      int cnt88 = 0;
      int cntF6 = 0;

      while(enabled) begin
        busy = 0;
        outputMbx.get(tr);
        busy = 1;

        $cast(ntr, tr);
        monitorID =  ntr.data[0];

        priority case (monitorID)
          8'h88 : begin
                    cnt88++;
                    $write("SORTER: COUNTER FL_OUTPUT_CONTROLLER: %d\n", cnt88);
                    mbx[0].put(tr); // FL Output Controller mailbox 
                  end
          8'hAA : mbx[1].put(tr); // Assertion Reporter mailbox
          8'hBB : mbx[2].put(tr); // Signal Reporter mailbox 
          8'hF6 : begin
                    cntF6++;
                    $write("SORTER: COUNTER FL_GEN_OUTPUT_CONTROLLER: %d\n", cntF6);
                    mbx[3].put(tr); // FL Generator Controller mailbox 
                  end  
          default : begin
                      $error("!!!SORTER: Unknown Output Controller Identifier!!!\n");
                      $finish();
                    end  
        endcase
      end  
    endtask : run
 endclass : Sorter
