/*
 * pcie_rd_responder.sv: PCIe Read responder
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobierský <kobiersky@liberouter.org>
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
 *
 *
 * TODO:
 *
 */

 // --------------------------------------------------------------------------
  // -- Memory Transaction Class
  // --------------------------------------------------------------------------
  typedef struct {
    logic [63:0] addr;
    byte data;
  } sPCIeMemoryTransaction;

  // --------------------------------------------------------------------------
  // -- Scoreboard Memory table
  // --------------------------------------------------------------------------
  class PCIeMemory;
     // ---------------------
     // -- Class Variables --
     // ---------------------
     byte assoc_mem[*];  // Associative memory
     semaphore sem;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      sem = new(1);
    endfunction
    
    // ------------------------------------------------------------------------
    // Add item to tabl
    task write(sPCIeMemoryTransaction item);
       lock();
       assoc_mem[item.addr] = item.data;
       unlock();
    endtask: write
    
    // ------------------------------------------------------------------------
    // Add item to table
    task read(logic [63:0] addr, ref sPCIeMemoryTransaction result);
      lock();
      result.addr      = addr;
      if (assoc_mem.exists(addr))
         result.data = assoc_mem[addr];
      else
         result.data = 8'h00; // Return zeros when reading from empty location
      result.data =  $urandom_range(0,255); // TODO : Random reading
      unlock();
    endtask: read
    
    // ------------------------------------------------------------------------
    // Lock table
    task lock();
       sem.get(1);
    endtask: lock

    // ------------------------------------------------------------------------
    // Unlock table
    task unlock();
       sem.put(1);
    endtask: unlock
    
    // ------------------------------------------------------------------------
    // Belongs to Switch address space
    task display();
       lock();
       $write("----------------------------------------------------------------\n");
       $write("-- PCIe Memory\n");
       $write("----------------------------------------------------------------\n");
       // TODO:
       $write("----------------------------------------------------------------\n");
       unlock();
    endtask: display
  endclass : PCIeMemory


  // --------------------------------------------------------------------------
  // -- Internal Bus Read Responder
  // --------------------------------------------------------------------------
  class PCIeReadResponder extends MonitorCbs;

    bit enabled;
    string inst;
    protected int stream_id;
    protected int scenario_id;
    protected int data_id;
    int           maxPayloadSize;
    PCIeMemory memory;
    tTransMbx transMbx;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (string inst, int stream_id = -1, tTransMbx transMbx = null);
      if (transMbx == null)  
        this.transMbx = new();     // Create own mailbox
      else
        this.transMbx = transMbx;  // Use created mailbox

      enabled      = 0;         // Disable generator by default
      inst         = inst;
      memory       = new;       // Create Internal Bus memory
      transMbx     = new;       // New Transaction mailbox
      stream_id    = stream_id; // Set stream id
      scenario_id  = -1;        // Set default scenario
      data_id      = 0;         // Set default data identifier
    endfunction
 
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      PcieTransaction pcie;
      $cast(pcie, transaction);
      if (enabled) begin
        case (pcie.transType)
          RD32, RD64:          
            processRD(pcie);
          WR32, WR64:
            processWR(pcie);
        endcase;
      end;
    endtask

    //-------------------------------------------------------------------------
    /*
     * Enable generator for creating n Instances.
     */
    task setEnabled();
      enabled = 1;
    endtask : setEnabled
    
    //-------------------------------------------------------------------------
    /*
     * Disable generator immediately.
     */
    task setDisabled();
      this.enabled = 0;
    endtask : setDisabled

    // -- Set Maximal Payload Size --------------------------------------------
    // Set Max. size of packet payload, See more p.342 of PCIe specification
    function void setMaxPayloadSize(integer size);
      case (size)
        128, 256, 512, 1024, 2048, 4096: 
          maxPayloadSize = size;          
        default
          $write("Unknown Max Payload Size");
      endcase;
    endfunction : setMaxPayloadSize

    // -- Process WR32, WR64 transaction --------------------------------------
    // Parse WR transaction into Memory transactions
    task processWR (PcieTransaction transaction);
       sPCIeMemoryTransaction memTr; // Memory transaction
       int dataIndex=0;
       int len = (transaction.length == 0) ? 1024 : transaction.length;
       for (int i=0; i<len; i++) begin
         for (int j=0; j < 4; j++) begin
            memTr.addr = transaction.address + i*4+j;
            memTr.data = transaction.data[dataIndex];
            if ( (i == 0 && transaction.firstBE[j] == 1) ||
                 (i != 0 && i == (len-1) && transaction.lastBE[j]==1) ||
                 (i > 0 && i < (len-1))
               ) begin
              memory.write(memTr);
              dataIndex = dataIndex + 1;
              end
            end
         end
    endtask

    // -- Process RD32, RD64 transaction --------------------------------------
    // Create Read Memory transaction and CPL IB transaction
    task processRD(PcieTransaction transaction);
       sPCIeMemoryTransaction memTr;         // Memory transaction
       int len;
       PcieTransaction cpl = new;
             
//       $write("POST_RX:\n");
//       transaction.display();

       cpl.stream_id    = stream_id;     // Set stream id
       cpl.scenario_id  = scenario_id;   // Set default scenario
       cpl.data_id      = data_id;       // Set instance count
       
       if (transaction.tag[7] == 1)  // Last only for last read request
         cpl.transType    = CPLD_LAST;
       else
         cpl.transType    = CPLD;

       cpl.tc           = transaction.tc;
       cpl.td           = transaction.td;
       cpl.ep           = transaction.ep;
       cpl.attr         = transaction.attr;
       cpl.length       = transaction.length;
       cpl.lowerAddr    = {transaction.address[6:2],getFirstByte(transaction)};
       cpl.requesterId  = transaction.requesterId;
       cpl.completerId  = $urandom_range(0,65535);
       cpl.tag          = transaction.tag;
       cpl.byteCount    = getByteCount(transaction);
       cpl.cplStatus    = CPLSTAT_OK;
       cpl.bcm          = 1'b0;
       cpl.supported    = 1'b1;
       cpl.error        = 1'b0;
       
       len = (cpl.byteCount == 0) ? 4096 : cpl.byteCount;
       cpl.data = new[len];
       for (int i=0; i<len; i++) begin
          memory.read(transaction.address[31:0] +getFirstByte(transaction)+ i, memTr);        
          cpl.data[i] = memTr.data;
          end
       splitCompletition(cpl);
    endtask

    // -- It splits completition transaction based on max payload size --------
    // Create Read Memory transaction and CPL IB transaction
    task splitCompletition(PcieTransaction cpl);
       PcieTransaction auxCpl;
       int dataIndex=0;
       int len = (cpl.byteCount == 0) ? 4096 : cpl.byteCount;
       int splitCountDiv = len / maxPayloadSize;
       int splitCountMod = len % maxPayloadSize;
       int splitCount = (splitCountMod > 0) ? splitCountDiv+1 : splitCountDiv;
//       $write("RECEIVING TRANSACTION FOR SPLITTING\n");
//       cpl.display();
       for (int i=0; i < splitCount; i++) begin
          if ( (i==0) && (i+1 == splitCount) ) begin // Generate first and last
//            $write("SPLITING FIRST AND LAST\n");
//            cpl.display();
            transMbx.put(cpl);
            end
          else if ((i+1 != splitCount)) begin // Generate first from multiple
            auxCpl = new;
            assert(cpl.copy(auxCpl));
            auxCpl.transType    = CPLD;
            auxCpl.data = new[maxPayloadSize-cpl.lowerAddr[1:0]];
            for (int j = 0; j < maxPayloadSize-cpl.lowerAddr[1:0]; j++)
              auxCpl.data[j] = cpl.data[dataIndex++];
            auxCpl.length = maxPayloadSize / 4;
            if (auxCpl.length == 4096)
              auxCpl.length = 0;
            cpl.byteCount = cpl.byteCount - maxPayloadSize + cpl.lowerAddr[1:0];
            cpl.lowerAddr = cpl.lowerAddr + maxPayloadSize - cpl.lowerAddr[1:0];
//            $write("SPLITING MULTIPLE BUT NOT LAST\n");
//            auxCpl.display();
            transMbx.put(auxCpl);
            end
          else if (i+1 == splitCount) begin // Generate last
            auxCpl = new;
            assert(cpl.copy(auxCpl));
            if (cpl.tag[7] == 1)  // Last only for last read request
              auxCpl.transType    = CPLD_LAST;
            else
              auxCpl.transType    = CPLD;
              
            auxCpl.data = new[cpl.byteCount];
            for (int j = 0; j < cpl.byteCount; j++)
              auxCpl.data[j] = cpl.data[dataIndex++];
            auxCpl.length = getDW(cpl.byteCount);
            if (auxCpl.length == 4096)
              auxCpl.length = 0;
//            $write("SPLITING LAST\n");
//            auxCpl.display();
            transMbx.put(auxCpl);
          end
       end
    endtask;
  
    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function int getDW(logic [11:0] len);
       int auxLen = (len == 0) ? 4096 : len;
       int lenDiv = auxLen / 4;
       int lenMod = auxLen % 4;
       getDW = (lenMod > 0) ? lenDiv+1 : lenDiv;
    endfunction;


    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function logic[1:0] getFirstByte(PcieTransaction transaction);
      case (transaction.firstBE)
        F1111: getFirstByte = 0;
        F1110: getFirstByte = 1;
        F1100: getFirstByte = 2;
        F1000: getFirstByte = 3;           
        F0111: getFirstByte = 0; 
        F0011: getFirstByte = 0; 
        F0110: getFirstByte = 1; 
        F0100: getFirstByte = 2; 
        F0010: getFirstByte = 1; 
        F0001: getFirstByte = 0; 
      endcase
    endfunction;

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function logic[1:0] getNotValidFirstByte(PcieTransaction transaction);
      case (transaction.firstBE)
        F1111: getNotValidFirstByte = 0;
        F1110: getNotValidFirstByte = 1;
        F1100: getNotValidFirstByte = 2;
        F1000: getNotValidFirstByte = 3;           
        F0111: getNotValidFirstByte = 1; 
        F0011: getNotValidFirstByte = 2; 
        F0110: getNotValidFirstByte = 2; 
        F0100: getNotValidFirstByte = 3; 
        F0010: getNotValidFirstByte = 3; 
        F0001: getNotValidFirstByte = 3; 
      endcase
    endfunction;

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function logic[1:0] getNotValidLastByte(PcieTransaction transaction);
      case (transaction.lastBE)
        L1111: getNotValidLastByte = 0;
        L0111: getNotValidLastByte = 1;
        L0011: getNotValidLastByte = 2;
        L0001: getNotValidLastByte = 3;
        L0000: getNotValidLastByte = 0;
      endcase
    endfunction; 

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function logic[11:0] getByteCount(PcieTransaction pcie);
      int length_10_0;
      int cmpl_len;
      length_10_0 = (pcie.length == 0) ? 1024 : pcie.length;
      cmpl_len    = length_10_0*4 - getNotValidFirstByte(pcie) - getNotValidLastByte(pcie);
      if (cmpl_len == 4096)
        cmpl_len = 0;
      getByteCount = cmpl_len;
    endfunction;

   
endclass : PCIeReadResponder
