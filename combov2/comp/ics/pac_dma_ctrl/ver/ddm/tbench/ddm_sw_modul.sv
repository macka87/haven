/*
 * \file ddm_sw_modul.sv
 * \brief Descriptor Download Manager Software Modul 
 * \date Copyright (C) 2009 CESNET
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name of the Company nor the names of its contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * This software is provided ``as is'', and any express or implied
 * warranties, including, but not limited to, the implied warranties of
 * merchantability and fitness for a particular purpose are disclaimed.
 * In no event shall the company or contributors be liable for any
 * direct, indirect, incidental, special, exemplary, or consequential
 * damages (including, but not limited to, procurement of substitute
 * goods or services; loss of use, data, or profits; or business
 * interruption) however caused and on any theory of liability, whether
 * in contract, strict liability, or tort (including negligence or
 * otherwise) arising in any way out of the use of this software, even
 * if advised of the possibility of such damage.
 *
 * $Id: ddm_sw_modul.sv 11285 2009-09-23 16:30:10Z kastovsky $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  /*!
   * \brief DDM Software Modul Class
   *
   * This class is responsible for generating signals to MI32 interface.
   *  
   */
  class DdmSoftwareModul;
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    bit       enabled;                 //! Modul is enabled
    int       swQueue[$];              //! Software Queue to store SW TailPointers and HW addresses
    string    inst;                    //! Modul identification
    virtual   iMi32.mi32_tb mi32;      //! MI32 interface
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // ------------------------------------------------------------------------
    //! Constructor
    /*
     * Create Software modul object
     */

    function new ( string inst, 
                   virtual iMi32.mi32_tb mi32
                 );      
      this.enabled     = 0;            // Modul is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.mi32        = mi32;         // Store pointer interface 
      
      this.mi32.mi32_cb.SW_DWR  <=0;
      this.mi32.mi32_cb.SW_ADDR <=0;
      this.mi32.mi32_cb.SW_RD   <=0;
      this.mi32.mi32_cb.SW_WR   <=0;
      this.mi32.mi32_cb.SW_BE   <=4'b1111; 
    
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Enable SW Modul
    /*
     * Enable modul and runs modul process
     */
    task setEnabled();
      enabled = 1; //! Modul Enabling
      fork         
        run();     //! Creating modul subprocess
      join_none;   //! Don't wait for ending
    endtask : setEnabled
        
    // ------------------------------------------------------------------------    
    //! Disable SW modul 
    /*
     * Disable generator
     */
    task setDisabled();
      enabled = 0; //! Disable modul
    endtask : setDisabled
    
    // ------------------------------------------------------------------------
    //! Run SW modul
    /*
     * Take HW address and TailPointer from mailbox and send this value via MI32
     */
    task run();
      int hwAddr;                  //! HW Address
      int value;                   //! Value
      int indicate;
     
      while (enabled) begin            //! Repeat while enabled        
        while (swQueue.size()==0) @(mi32.mi32_cb);
        hwAddr = swQueue.pop_front();
        value  = swQueue.pop_front();
        writeMI32(hwAddr, value);
        @(mi32.mi32_cb);
	if ((hwAddr % 32) == 0)
		hwAddr += 4;
        readMI32(hwAddr,indicate);

        if ((indicate == 0) || (indicate == 1)) begin
          assert (indicate == value) 
          else $error("Error in Status Register values.");
        end
      end
    endtask : run

    // ------------------------------------------------------------------------
    //! Write MI32
    /*
     * Writes on MI32
     */
    task writeMI32(int address, int value);
      mi32.mi32_cb.SW_ADDR <= address;
      mi32.mi32_cb.SW_DWR <= value;
      mi32.mi32_cb.SW_WR <= 1;
      @(mi32.mi32_cb);
     
      waitForArdy();      
      mi32.mi32_cb.SW_WR <= 0;
    endtask : writeMI32
    
    // ------------------------------------------------------------------------
    //! Read MI32 
    /*
     * Reads from MI32
     */ 
    task readMI32(int address, output int value);
      mi32.mi32_cb.SW_ADDR <= address;
      mi32.mi32_cb.SW_RD <= 1;
     
      waitForArdy();
      mi32.mi32_cb.SW_RD <= 0;
      
      waitForDrdy();
      value = mi32.mi32_cb.SW_DRD;
    endtask : readMI32        
   
    // ------------------------------------------------------------------------ 
    //! Wait For Ardy
    /*
     * Waits until SW_ARDY
     */
    task waitForArdy();
      //do begin
      //  @(mi32.mi32_cb);
      //end while (!mi32.mi32_cb.SW_ARDY);
      while (!mi32.mi32_cb.SW_ARDY) @(mi32.mi32_cb);
    endtask : waitForArdy  
    
    // ------------------------------------------------------------------------
    //! Wait For Drdy
    /*
     * Waits until SW_DRDY
     */
    task waitForDrdy();
      while (!mi32.mi32_cb.SW_DRDY) @(mi32.mi32_cb);
    endtask : waitForDrdy  
    
endclass : DdmSoftwareModul
