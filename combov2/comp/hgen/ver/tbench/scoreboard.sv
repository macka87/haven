/*
 * scoreboard.sv: Frame Link Scoreboard
 * Copyright (C) 2009 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
 
import test_pkg::*;
import sv_common_pkg::*;
import sv_fl_pkg::*;
  
   class BJHModel;
      typedef bit[31:0] mytype;
   
      mytype init;
    
      function new(mytype init);
         this.init = init;
      endfunction
    
      function void mix(inout mytype a, inout mytype b, inout mytype c);
         a -= b; a -= c; a ^= (c>>13);
         b -= c; b -= a; b ^= (a<<8);
         c -= a; c -= b; c ^= (b>>13);
         a -= b; a -= c; a ^= (c>>12);
         b -= c; b -= a; b ^= (a<<16);
         c -= a; c -= b; c ^= (b>>5);
         a -= b; a -= c; a ^= (c>>3);
         b -= c; b -= a; b ^= (a<<10);
         c -= a; c -= b; c ^= (b>>15);
      endfunction
      
      function bit[95:0] hash(byte unsigned data[]);
         mytype a,b,c,len, i;
   
         /* Set up the internal state */
         len = data.size();
         a = 32'h9e3779b9;  /* the golden ratio; an arbitrary value */
         b = 32'h9e3779b9;  /* the golden ratio; an arbitrary value */
         c = this.init;         /* the previous hash value */
         i = 0;                 /* index into data array */ 
      
         /*---------------------------------------- handle most of the key */
         while (len >= 12)
         begin
            a += (mytype'(data[i + 0]) + (mytype'(data[i + 1]) << 8) + (mytype'(data[i + 2]) << 16) + (mytype'(data[i + 3]) << 24));
            b += (mytype'(data[i + 4]) + (mytype'(data[i + 5]) << 8) + (mytype'(data[i + 6]) << 16) + (mytype'(data[i + 7]) << 24));
            c += (mytype'(data[i + 8]) + (mytype'(data[i + 9]) << 8) + (mytype'(data[i + 10]) << 16) + (mytype'(data[i + 11]) << 24));
            mix(a,b,c);
            i += 12; len -= 12;
         end
      
         /*------------------------------------- handle the last 11 bytes */
         c += data.size();

         if (len == 11)
         begin
            c += (mytype'(data[i + 10]) << 24);
            len--;
         end
         
         if (len == 10)
         begin
            c += (mytype'(data[i + 9]) << 16);
            len--;
         end
         
         if (len == 9)
         begin
            c += (mytype'(data[i + 8]) << 8);
            len--;
         end
         
         if (len == 8)
         begin
            b += (mytype'(data[i + 7]) << 24);
            len--;
         end
         
         if (len == 7)
         begin
            b += (mytype'(data[i + 6]) << 16);
            len--;
         end
         
         if (len == 6)
         begin
            b += (mytype'(data[i + 5]) << 8);
            len--;
         end
         
         if (len == 5)
         begin
            b += mytype'(data[i + 4]);
            len--;
         end
         
         if (len == 4)
         begin
            a += (mytype'(data[i + 3]) << 24);
            len--;
         end
         
         if (len == 3)
         begin
            a += (mytype'(data[i + 2]) << 16);
            len--;
         end
         
         if (len == 2)
         begin
            a += (mytype'(data[i + 1]) << 8);
            len--;
         end
         
         if (len == 1)
         begin
            a += mytype'(data[i + 0]);
            len--;
         end
         
         mix(a,b,c);
         
         return {a,b,c};
      endfunction
   
   endclass : BJHModel
  

   // --------------------------------------------------------------------------
   // -- Frame Link Driver Callbacks
   // --------------------------------------------------------------------------
   class ScoreboardDriverCbs extends DriverCbs;

      // ---------------------
      // -- Class Variables --
      // ---------------------
      TransactionTable sc_table;
      int              flow_id_width;
      bit[31:0]        hgen_init;
      bit[63:0]        hgen_mask;

      // -------------------
      // -- Class Methods --
      // -------------------

      // -- Constructor ---------------------------------------------------------
      // Create a class 
      function new (TransactionTable sc_table, int flow_id_width, bit[63:0] hgen_init, bit[63:0] hgen_mask);
         this.sc_table = sc_table;
         this.flow_id_width = flow_id_width;
         this.hgen_init = hgen_init;
         this.hgen_mask = hgen_mask;
      endfunction
    
      virtual task pre_tx(ref Transaction transaction, string inst);

      endtask: pre_tx
    
      // ------------------------------------------------------------------------
      // Function is called after is transaction sended 
      virtual task post_tx(Transaction transaction, string inst);
         FrameLinkTransaction tr;
         FrameLinkTransaction res;
         bit[95:0] result;
         BJHModel bjh;
         byte unsigned data[];
         // BJH parametrs       
         bjh = new(hgen_init);
         $cast(tr,transaction);
         data = new[tr.data[0].size];

         // input data masking
         for(int i = 0; i<tr.data[0].size; i++)
         begin
            if(hgen_mask[i]==0)
            data[i]=8'h0;
            else
            data[i]= tr.data[0][i];
         end;
         // bjh compute
         result = bjh.hash(data);
         // output FrameLink frame assembly
         res = new;
         res.data = new[1];
         res.packetCount = 1;
         res.data[0] = new[tr.data[0].size + flow_id_width/8];
         for(int i=0; i < tr.data[0].size; i++)
            res.data[0][i+flow_id_width/8] = tr.data[0][i];
         for(int i = 4; i < flow_id_width/8; i++)
            res.data[0][i] =  '0;
         res.data[0][11] = result[95:88];
         res.data[0][10] = result[87:80];
         res.data[0][9] = result[79:72];
         res.data[0][8] = result[71:64];
         res.data[0][7] = result[63:56];
         res.data[0][6] = result[55:48];
         res.data[0][5] = result[47:40];
         res.data[0][4] = result[39:32];
         res.data[0][3] = result[31:24];
         res.data[0][2] = result[23:16];
         res.data[0][1] = result[15:8];
         res.data[0][0] = result[7:0];
         sc_table.add(res);
      endtask
   
      endclass : ScoreboardDriverCbs
   
   
   // --------------------------------------------------------------------------
   // -- Frame Link Monitor Callbacks
   // --------------------------------------------------------------------------
   class ScoreboardMonitorCbs extends MonitorCbs;
      
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
         bit status=0;
         // transaction.display("MONITOR");
         sc_table.remove(transaction, status);
         if (status==0)begin
            $write("Unknown transaction received from monitor %d\n", inst);
            transaction.display(); 
            sc_table.display();
            $stop;
         end;
      endtask
   
   
   endclass : ScoreboardMonitorCbs
   
   // -- Constructor ---------------------------------------------------------
   // Create a class 
   // --------------------------------------------------------------------------
   // -- Scoreboard
   // --------------------------------------------------------------------------
   class Scoreboard;
      // ---------------------
      // -- Class Variables --
      // ---------------------
      TransactionTable     scoreTable;
      ScoreboardMonitorCbs monitorCbs;
      ScoreboardDriverCbs  driverCbs;
      DriverCbs            mi32DriverCbs;
   
      // -- Constructor ---------------------------------------------------------
      // Create a class 
      function new (int flow_id_width, bit[31:0] hgen_init, bit[63:0] hgen_mask);
         this.scoreTable = new;
         this.monitorCbs = new(scoreTable);
         this.driverCbs  = new(scoreTable,flow_id_width, hgen_init, hgen_mask);
         this.mi32DriverCbs = new;
      endfunction
   
      // -- Display -------------------------------------------------------------
      // Create a class 
      task display();
         scoreTable.display();
      endtask
   
   endclass : Scoreboard
   
