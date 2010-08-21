/*
 * rx_sw_modul.sv: Software Modul for RX DMA Controller
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
 * $Id: rx_sw_modul.sv 12979 2010-02-26 16:13:08Z kastovsky $
 *
 * TODO:
 *
 */
 
  // --------------------------------------------------------------------------
  // -- Software Modul Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to MI32 interface.
   * It synchronize startPtr and endPtr between DUT and TxDmaCtrlDriver class.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. 
   */
  class RxSoftwareModul #(int pFlows = 2, int pPageSize = 4092, int pPageCount = 3);
    
    // ----------------------
    // -- Class Attributes --
    // ----------------------
    string    inst;                             // Modul identification
    bit       enabled;                          // Modul is enabled
    virtual iMi32.tb mi32;
    
    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string inst, 
                   virtual iMi32.tb mi32
                 );      
      this.enabled     = 0;            // Driver is disabled by default
      this.inst        = inst;         // Store driver identifier
      this.mi32        = mi32;         // Store pointer interface 
      
      this.mi32.cb.DWR  <=0;
      this.mi32.cb.ADDR <=0;
      this.mi32.cb.RD   <=0;
      this.mi32.cb.WR   <=0;
      this.mi32.cb.BE   <=4'b1111;      
    endfunction: new          
    
    // -- Get End Ptr ----------------------------------------------------------
    // Gets End pointer
    task getEndPtr(int ctrlNo, output int endPtr);
      logic [31:0] ctrlAddr = ctrlNo<<6;            // Controller Address
      
      readMI32(ctrlAddr+(3<<2),endPtr);
    endtask : getEndPtr
    
    // -- Set Start Ptr ----------------------------------------------------------
    // Sets start pointer
    task setStrPtr(int ctrlNo, int strPtr);
      logic [31:0] ctrlAddr = ctrlNo<<6;            // Controller Address
      
      writeMI32(ctrlAddr+(2<<2),strPtr);
    endtask : setStrPtr
    
    // -- Init Ctrl -----------------------------------------------------------
    // Initiate controllers
    task initCtrl();
      logic [31:0] ctrlAddr = 0;            // Controller Address
      
      @(mi32.cb);
      for (int i=0; i<pFlows; i++)
      begin
        ctrlAddr = i<<6;
        
        // Set CONTROL register (init)
        writeMI32(ctrlAddr+(0<<2),4);
        
        // Set SW_STR_PRT register
        writeMI32(ctrlAddr+(2<<2),0);
        
        // Set SW_END_PTR register
        writeMI32(ctrlAddr+(3<<2),0);
        
        // Set SW_BUFF_MASK register
        writeMI32(ctrlAddr+(4<<2),pPageCount*pPageSize-1);
        
        // Set INTERRUPT register
        writeMI32(ctrlAddr+(5<<2),0);
        
        // Set TIMEOUT register
        writeMI32(ctrlAddr+(6<<2),0);
        
        // Set CONTROL register (run)
        writeMI32(ctrlAddr+(0<<2),1);
      end  
    endtask : initCtrl
    
    // -- Write MI32 ----------------------------------------------------------
    // Writes on MI32
    task writeMI32(int address, int value);
      mi32.cb.ADDR <= address;
      mi32.cb.DWR <= value;
      mi32.cb.WR <= 1;
      
      waitForArdy();      
      mi32.cb.WR <= 0;
    endtask : writeMI32
    
    // -- Read MI32 -----------------------------------------------------------
    // Reads from MI32
    task readMI32(int address, output int value);
      mi32.cb.ADDR <= address;
      mi32.cb.RD <= 1;
      
      waitForArdy();
      mi32.cb.RD <= 0;
      
      waitForDrdy();
      value = mi32.cb.DRD;
    endtask : readMI32        
    
    // -- Wait For Ardy -------------------------------------------------------
    // Waits until ARDY
    task waitForArdy();
      do begin
        @(mi32.cb);
      end while (!mi32.cb.ARDY);
    endtask : waitForArdy  
    
    // -- Wait For Drdy -------------------------------------------------------
    // Waits until DRDY
    task waitForDrdy();
      while (!mi32.cb.DRDY) @(mi32.cb);
    endtask : waitForDrdy  
    
  endclass : RxSoftwareModul 
