/*!
 * \file dma_modul_sw.sv
 * \brief DMA Modul Software 
 * \author Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 * \author Marek Santa <xsanta06@stud.fit.vutbr.cz> 
 * \date 2009
 */  
 /*   
 * Copyright (C) 2009 CESNET
 * 
 * LICENSE TERMS  
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
 * $$
 *
 * TODO:
 *
 */
 
  import sv_dma_module_gen_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- DMA Modul Software Class
  // --------------------------------------------------------------------------
  
  /*!
   * \brief DMA Modul Software Class
   *    
   * This class is responsible for creating RAM, where transaction are stored 
   * and received. Unit must be enabled by "setEnable()" function call. 
   * Monitoring can be stoped by "setDisable()" function call.
   * 
   * \param pDataWidth - data width
   * \param pFLows - count of flows
   * \param pPageSize - size of one page
   * \param pPageCount - count of size in one flow    
   */
  class DmaModuleSW #(int pDataWidth = 64, int pFlows = 4, int pPageSize = 4096, int pPageCount = 2);
    
    // -- Private Class Atributes --
    
    //! RAM memory 
    logic[pDataWidth-1:0] ram[];   
                  
    // Data width in Bytes  
    const int pDataWidthByte = pDataWidth/8;
    // Page size in words
    const int pPageSizeWord  = pPageSize/(pDataWidth/8);
    
    // -- Public Class Methods --

    // ------------------------------------------------------------------------
    //! Constructor 
    /*!
     * Creates modul object and sets default values of InternalBus interface signals 
     */
    function new ();
      int pageSizeCounter = 0;
      int descPage = 0;
      
      // RAM memory = space for data  +  space for descriptors
      int spaceForDesc = 2*pFlows*(pPageCount/(pPageSizeWord-1)+1)*pPageSizeWord;
      ram    = new[2*pFlows*pPageCount*pPageSizeWord + spaceForDesc]; 

      // Set descriptors type 0
      for (int i=0; i<pPageCount; i++) begin
        if (i!=0 && i%(pPageSize/pDataWidthByte-1)==0) begin
          descPage++;
        end   
        for (int j=0; j<2*pFlows; j++) begin
          ram[(2*pFlows*descPage+j)*pPageSizeWord + (i%(pPageSize/pDataWidthByte-1))] = spaceForDesc*pDataWidthByte + pageSizeCounter;
          pageSizeCounter += pPageSize;
        end  
      end  
      
      // Set descriptors type 1
      descPage=0;
      
      for (int i=0; i<pPageCount/pPageSizeWord; i++) begin
        for (int j=0; j<2*pFlows; j++) begin
          ram[(2*pFlows*(descPage)+j)*pPageSizeWord + pPageSizeWord-1] = (2*pFlows*(descPage+1)+j)*pPageSize+1;   
        end
        descPage++;
      end  

      for (int i=0; i<2*pFlows; i++) begin
        ram[(2*pFlows*descPage+i)*pPageSizeWord+(pPageCount%pPageSizeWord+pPageCount/pPageSizeWord)] = i*pPageSize+1;
      end
    endfunction: new          
    
    // ------------------------------------------------------------------------
    //! Get Data
    /*!
     * Get word of data from RAM
     * \param tr - InternalBus transaction     
     */      
    function void getData(InternalBusTransaction tr);
      int words; // number of words in RAM
      int counter=0;
      longint address=tr.globalAddr/pDataWidthByte;
      
      if (tr.length==0) begin
        words=512;
        tr.data = new[4096];
      end
      else begin
        words = (tr.length/pDataWidthByte)+(tr.length%pDataWidthByte);
        tr.data = new[tr.length];
      end  

      do begin
        for (int i=0;i<pDataWidthByte;i++)
          for (int j=0;j<8;j++)
            tr.data[i+counter*pDataWidthByte][j] = ram[address+counter][i*pDataWidthByte+j];
        counter++;    
      end while(counter!=words);  
    endfunction : getData
    
    // ------------------------------------------------------------------------
    //! Store Data 
    /*!
     * Store word of data into RAM
     * \param tr - InternalBus transaction        
     */     
    function void storeData(InternalBusTransaction tr);
      int counter=0;
      int words; // number of words in RAM
      longint address=tr.globalAddr/pDataWidthByte;
      
      if (tr.length==0) 
        words=512;
      else
        words = (tr.length/pDataWidthByte)+(tr.length%pDataWidthByte);
        
      do begin
        for (int i=0;i<pDataWidthByte;i++)
          for (int j=0;j<8;j++)
            ram[address+counter][i*pDataWidthByte+j]= tr.data[i+counter*pDataWidthByte][j];
        counter++;    
      end while(counter!=words);
    endfunction : storeData

    // ------------------------------------------------------------------------
    //! Store Data Word 
    /*!
     * Store word of data into RAM
     * \param txIfcNo - TX interface number
     * \param bufferAddress - buffer address
     * \param data - data               
     */      
    function void storeBufferData(int txIfcNo, int unsigned bufferAddress, 
                                  byte data[]);
      
      // Ordinal number of descriptor
      int descNo = (bufferAddress/pDataWidthByte)/pPageSizeWord;
      // Address of descriptor
      int descAddr = descNo/(pPageSizeWord-1)*2*pFlows*pPageSizeWord + (2*txIfcNo+1)*pPageSizeWord + descNo%(pPageSizeWord-1);
      // Data address offset
      int offset = (bufferAddress/pDataWidthByte)%pPageSizeWord;
      
      // Global address
      longint unsigned address = ram[descAddr]/pDataWidthByte+offset;
      // Store data
      for (int i=0; i<pDataWidthByte; i++)
        for (int j=0; j<8; j++)
          ram[address][i*pDataWidthByte+j] = data[i][j];    
    endfunction: storeBufferData   
    
    // ------------------------------------------------------------------------
    //! Receive Data Word 
    /*!
     * Receive word of data from RAM
     * \param txIfcNo - RX interface number
     * \param bufferAddress - buffer address
     * \param data - data               
     */     
    function void receiveBufferData(int rxIfcNo, int unsigned bufferAddress, 
                                    inout byte data[]);
      
      // Ordinal number of descriptor
      int descNo = (bufferAddress/pDataWidthByte)/pPageSizeWord;
      // Address of descriptor
      int descAddr = descNo/(pPageSizeWord-1)*2*pFlows*pPageSizeWord + 2*rxIfcNo*pPageSizeWord + descNo%(pPageSizeWord-1);
      // Data address offset
      int offset = (bufferAddress/pDataWidthByte)%pPageSizeWord;
      
      // Global address
      longint unsigned address = ram[descAddr]/pDataWidthByte+offset;
      // Receive data
      for (int i=0; i<pDataWidthByte; i++)
        for (int j=0; j<8; j++)
          data[i][j] = ram[address][i*pDataWidthByte+j];    
    endfunction: receiveBufferData                                        
        
    // ------------------------------------------------------------------------
    //! RAM Display 
    /*!
     * Displays RAM content
     */      
    function void ramDisplay(int spaceForDesc, bit full=0);
      $write ("-----------------------------------\n");
      $write ("-- DESCRIPTORS\n");
      $write ("-----------------------------------\n");
      
      for (int i=0; i<spaceForDesc; i++)
      begin
        if (i%pPageSizeWord==0) $write("\n\n");
        $write("%4x: ",i*(pDataWidth/8));
        $write("%x ",ram[i]);
        $write("\n");
      end 
      
      if (full) begin
        $write ("-----------------------------------\n");
        $write ("-- RAM\n");
        $write ("-----------------------------------\n");
        
        for (int i=ram.size-spaceForDesc; i<ram.size; i++)
        begin
          if (i%pPageSizeWord==0) $write("\n\n");
          $write("%4x: ",i*(pDataWidth/8));
          $write("%x ",ram[i]);
          $write("\n");
        end 
      end
        
      $write ("-----------------------------------\n"); 
    endfunction : ramDisplay 
    
    // ------------------------------------------------------------------------
    //! RAM Display Part
    /*!
     * Displays part of RAM content
     */      
    function void ramDisplayPart(int lowAddr, int highAddr);
      $write ("-----------------------------------\n");
      $write ("-- RAM\n");
      $write ("-----------------------------------\n");
      
      for (int i=lowAddr; i<highAddr; i++)
      begin
        if (i%pPageSizeWord==0) $write("\n\n");
        $write("%4x: ",i*(pDataWidth/8));
        $write("%x ",ram[i]);
        $write("\n");
      end 
    endfunction : ramDisplayPart 
    
  endclass : DmaModuleSW
