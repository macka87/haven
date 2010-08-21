/*
 * ib2pcie_check.sv: IB2PCIE check
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

import sv_common_pkg::*;
import sv_ib_pkg::*;
import sv_pcie_pkg::*;
  
  // --------------------------------------------------------------------------
  // -- Pcie2Ib Checker Driver Callbacks
  // --------------------------------------------------------------------------
  class Ib2PcieCheckDriverCbs extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;

    logic	[7:0]  bus_number = 0;
    logic	[4:0]  device_number = 0;
    logic	[2:0]  function_number = 0;
    int maxReadRequestSize = 0;
    int maxPayloadSize = 0;

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called before is transaction sended 
    // Allow modify transaction before is sended
    virtual task post_tx(Transaction transaction, string inst);
//      $write("PRE_TX_IB:\n");
//      transaction.display();
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction sended 
    virtual task pre_tx(ref Transaction transaction, string inst);
      PcieTransaction splited;
      PcieTransaction auxPcie = ib2pcie(transaction);
      int length_10_0 = (auxPcie.length == 0) ? 1024 : auxPcie.length;

//      $write("PRE_TX_IB:\n");
//      transaction.display();

      case (auxPcie.transType)
         WR32, WR64, RDCL, CPLD: begin // Split based on payload size
            
//            if (length_10_0 > maxPayloadSize/4) begin  // TODO: AFTER TESTING REMOVE
//              $write("SPLITING PCIe transaction:\n");     // TODO: AFTER TESTING REMOVE
//              auxPcie.display();                          // TODO: AFTER TESTING REMOVE
//              end                                         // TODO: AFTER TESTING REMOVE

            while (length_10_0 > maxPayloadSize/4) begin
               splited = splitWithData(auxPcie);
//               $write("Adding transaction part to output:\n"); // TODO: AFTER TESTING REMOVE
//               splited.display();                              // TODO: AFTER TESTING REMOVE
               sc_table.add(splited);
               length_10_0 = (auxPcie.length == 0) ? 1024 : auxPcie.length;
               end

//            $write("Adding transaction part to output:\n");   // TODO: AFTER TESTING REMOVE
//            auxPcie.display();                                // TODO: AFTER TESTING REMOVE
            sc_table.add(auxPcie);
            end

        RD32, RD64: begin // Split based on payload size

//            if (length_10_0 > maxPayloadSize/4) begin  // TODO: AFTER TESTING REMOVE
//              $write("SPLITING PCIe transaction:\n");     // TODO: AFTER TESTING REMOVE
//              auxPcie.display();                          // TODO: AFTER TESTING REMOVE
//              end                                         // TODO: AFTER TESTING REMOVE

           while (length_10_0 > maxReadRequestSize/4) begin
               splited = splitRead(auxPcie);
//               $write("Adding transaction part to output:\n"); // TODO: AFTER TESTING REMOVE
//               splited.display();                              // TODO: AFTER TESTING REMOVE
               sc_table.add(splited);
               length_10_0 = (auxPcie.length == 0) ? 1024 : auxPcie.length;
               end

//            $write("Adding transaction part to output:\n"); // TODO: AFTER TESTING REMOVE
//            auxPcie.display();                              // TODO: AFTER TESTING REMOVE
            sc_table.add(auxPcie);
            end
        endcase

    endtask

    // ------------------------------------------------------------------------
    // Function transform PCIE transaction to IB transaction 
    function PcieTransaction splitWithData(PcieTransaction tr);
       int dataLength;
       PcieTransaction splited = new;
       PcieTransaction trCopy = new;

       // Create part of transaction
       assert(tr.copy(splited));
       splited.length = maxPayloadSize/4;
       splited.lastBE = L1111;
   
       if (splited.transType == WR32 || splited.transType == WR64)
          dataLength = maxPayloadSize-splited.minusBE();
       else  
          dataLength = maxPayloadSize-splited.lowerAddr[1:0];

       splited.data = new[dataLength];
//       $write("datalen:%d maxpayload:%d minusbe%d\n", dataLength, maxPayloadSize, splited.minusBE());
       for (int i = 0; i < dataLength; i++)
         splited.data[i] = tr.data[i];
       
       // Remove sended part from input transaction
       assert(tr.copy(trCopy));

       // Remove sended data
       tr.data = new[trCopy.data.size-dataLength];
       for (int i = 0; i < tr.data.size; i++)
         tr.data[i] = trCopy.data[i+dataLength];

       // Fix Address (WR)
       tr.address = tr.address+maxPayloadSize;
       // Fix First BE (WR)
       tr.firstBE = F1111;
       // Fix Length
       tr.length = tr.length - maxPayloadSize/4;
       // Lower Address
       tr.lowerAddr = 0;
       // Byte count
       tr.byteCount = tr.byteCount - dataLength;

       if (tr.length == 1) begin
          tr.firstBE = tr.lastBE;
          tr.lastBE = L0000;
          end
       

       // Return result
       splitWithData = splited;
    endfunction;


    // ------------------------------------------------------------------------
    // Function transform PCIE transaction to IB transaction 
    function PcieTransaction splitRead(PcieTransaction tr);
       PcieTransaction splited = new;
       PcieTransaction trCopy = new;

       // Create part of transaction
       assert(tr.copy(splited));
       splited.length = maxReadRequestSize/4;
       splited.lastBE = L1111;

       // Remove sended part from input transaction
       assert(tr.copy(trCopy));

       // Fix Address (WR)
       tr.address = tr.address+maxReadRequestSize;
       // Fix First BE (WR)
       tr.firstBE = F1111;
       // Fix Length
       tr.length = tr.length - maxReadRequestSize/4;
     
       if (tr.length == 1) begin
          tr.firstBE = tr.lastBE;
          tr.lastBE = L0000;
          end

       // Return result
       splitRead = splited;
 
    endfunction;

    // ------------------------------------------------------------------------
    // Function transform PCIE transaction to IB transaction 
    function PcieTransaction ib2pcie(input Transaction tr);
      InternalBusTransaction ib;
      PcieTransaction result = new;
      $cast(ib, tr);

      // Get transaction type
      case (ib.transType)
        L2GW: begin
                if (ib.globalAddr[63:32] == 0)
                  result.transType = WR32;
                else
                  result.transType = WR64;
               end
        G2LR: begin
                if (ib.globalAddr[63:32] == 0)
                  result.transType = RD32;
                else
                  result.transType = RD64;
               end
        RDCL: result.transType = CPLD;
        default: $write("IB2PCIE Check received unsupported transaction\n");
      endcase;

      // Supported
      result.supported = 1;        
      // Error
      result.error = 0;
      // Set tag ( IN THIS TEST WE DON'T CARE )
      result.tag = 16'h0000;
      // Traffic Class
      result.tc = 0;
      // Get firstBE
      result.firstBE = getFirstBe(ib);
      // Get lastBE
      result.lastBE  = getLastBe(ib);
      // Address
      result.address = {ib.globalAddr[63:2], 2'b00};
      // Lower Address
      result.lowerAddr = {ib.localAddr[6:2], ib.globalAddr[1:0]};
      // Byte Count
      result.byteCount = ib.length;

      // Requester ID & Completer ID
      if (result.transType == CPLD) begin
        result.completerId = {bus_number, device_number, function_number};
        result.requesterId = 0; // Don't Check
        end
      else
        result.requesterId = {bus_number, device_number, function_number};
 
      // Get length
      result.length = getLength(ib);

      if (ib.transType == L2GW || ib.transType == RDCL)
        result.data=ib.data;

      ib2pcie = result;
 
    endfunction;

    // ------------------------------------------------------------------------
    // Function return firstBE for write or read request 
    function logic [3:0] getFirstBe(input InternalBusTransaction ib);
       int first_byte_valid;
       int last_byte_valid;
       int length_10_0 = (ib.length == 0) ? 4096 : ib.length;
       logic [3:0] result = 4'b0000;

       first_byte_valid = ib.globalAddr[1:0];
       if (length_10_0 <= 4) begin
         last_byte_valid = length_10_0+ib.globalAddr[1:0]-1;
         if (last_byte_valid >3)
           last_byte_valid = 3;
         end
       else
         last_byte_valid = 3;

       for (int i=first_byte_valid; i<=last_byte_valid;i++)
         result[i]=1'b1;
        getFirstBe = result;
      endfunction;
    
    // ------------------------------------------------------------------------
    // Function return firstBE for write or read request 
     function logic [3:0] getLastBe(input InternalBusTransaction ib);
       int first_byte_valid;
       int last_byte_valid;
       int length_10_0 = (ib.length == 0) ? 4096 : ib.length;
       logic [3:0] result = 4'b0000;

       length_10_0 = length_10_0 + ib.globalAddr[1:0];

       if (length_10_0 <=4) 
         result = 4'b0000;
       else begin
         last_byte_valid = length_10_0%4;
         if (last_byte_valid == 0)
           last_byte_valid = 3;
         else
           last_byte_valid = last_byte_valid-1;

         for (int i=0; i<=last_byte_valid;i++)
           result[i]=1'b1;
         end 
         getLastBe = result;
    endfunction;

    // ------------------------------------------------------------------------
    // Function return length in bytes of read, write or completition 
    function int getLength(input InternalBusTransaction ib);
      int result;
      int length_10_0 = (ib.length == 0) ? 4096 : ib.length;
      length_10_0 = length_10_0 + ib.globalAddr[1:0]; // Used for valid bytes
      result = (length_10_0 / 4);
      if ( (length_10_0 %4) > 0)
        result = result+1;
      getLength = result;
    endfunction;

   endclass : Ib2PcieCheckDriverCbs


  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  class Ib2PcieCheckMonitorCbs extends MonitorCbs;
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    TransactionTable sc_table;
    
    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new (TransactionTable sc_table);
      this.sc_table = sc_table;
    endfunction
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    
    virtual task post_rx(Transaction transaction, string inst);
      PcieTransaction pcie;
      bit status=0;
//      $write("POST_RX_PCIE:\n");
//      transaction.display();
      
      $cast(pcie, transaction);
      // Read, Write compare
      if (pcie.transType != CPLD_LAST && pcie.transType != CPLD)
        sc_table.remove(transaction, status, CMP_IB2PCIE_RD_WR);
      else // Completition compare (don't look at adresses)
        sc_table.remove(transaction, status, CMP_IB2PCIE_CMPL);
     
      if (status==0)begin
         $write("Unknown transaction received from monitor %d\n", inst);
         $timeformat(-9, 3, " ns", 8);
         $write("Time: %t\n", $time);
         transaction.display(); 
         sc_table.display();
         $stop;
      end;
    endtask
  endclass : Ib2PcieCheckMonitorCbs



  // -- Constructor ---------------------------------------------------------
  // Create a class 
  // --------------------------------------------------------------------------
  // -- Scoreboard
  // --------------------------------------------------------------------------
  class Ib2PcieCheck;
    // ---------------------
    // -- Class Variables --
    // ---------------------

    TransactionTable       scoreTable;
    Ib2PcieCheckMonitorCbs monitorCbs;
    Ib2PcieCheckDriverCbs  driverCbs;

    // -- Constructor ---------------------------------------------------------
    // Create a class 
    function new ();
      this.scoreTable = new;
      this.monitorCbs = new(scoreTable);
      this.driverCbs  = new(scoreTable);
    endfunction


    // -- Set Maximal Payload Size --------------------------------------------
    // Set Max. size of packet payload, See more p.342 of PCIe specification
    function void setMaxPayloadSize(integer size);
      case (size)
        128, 256, 512, 1024, 2048, 4096: 
          driverCbs.maxPayloadSize = size;          
        default
          $write("Unknown Max Payload Size");
      endcase;
    endfunction : setMaxPayloadSize

    // -- Set Maximal Read Request size ---------------------------------------
    // Set Max. read request size of packet payload, See more p.375 of PCIe specification
    function void setMaxReadRequestSize(integer size);
      case (size)
        128, 256, 512, 1024, 2048, 4096: 
          driverCbs.maxReadRequestSize = size;          
        default
          $write("Unknown Max Read Request Size");
      endcase;
    endfunction : setMaxReadRequestSize

    // -- Set Bridge Identification -------------------------------------------
    function void setBridgeId(logic	[7:0] bus_number, logic	[4:0] device_number, logic	[2:0] function_number);
      driverCbs.bus_number      = bus_number;
      driverCbs.device_number   = device_number;
      driverCbs.function_number = function_number;
    endfunction : setBridgeId


    // -- Display -------------------------------------------------------------
    // Create a class 
    task display();
      scoreTable.display();
    endtask
  endclass : Ib2PcieCheck

