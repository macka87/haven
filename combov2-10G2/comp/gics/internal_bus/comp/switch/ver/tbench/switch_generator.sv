/*
 * switch_generator.sv: Generator of "corner case" transactions for switch
 * Copyright (C) 2009 CESNET
 * Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
 * $Id: switch_generator.sv 12297 2009-12-16 18:17:27Z washek $
 *
 * TODO:
 *
 */

package switch_generator_pkg;
  
  import sv_common_pkg::*;
  import ib_common_pkg::InternalBusTransaction;
  import ib_params_pkg::*;
  
  class SwitchGenerator #(pIbSwitchGenerics G = dIbSwitchGenerics)
                                                             extends Generator;
    int addr;
    rand bit[31:0] base_addr;
    rand int       offset;
    rand bit       offset1;
    
    parameter int PORT1_BASE  = G.PORT1_BASE;
    parameter int PORT2_BASE  = G.PORT2_BASE;
    parameter int PORT1_TOP   = G.PORT1_BASE  + G.PORT1_LIMIT  - 1;
    parameter int PORT2_TOP   = G.PORT2_BASE  + G.PORT2_LIMIT  - 1;
    
    constraint c {
      base_addr inside {PORT1_BASE, PORT2_BASE,
                        PORT1_TOP,  PORT2_TOP};
      
      offset inside {0, 8, 16, 32, 64, 128, 256, 65536};
    }
    
    function new(string inst, int stream_id = -1, tTransMbx transMbx = null);
      super.new(inst, stream_id, transMbx);
    endfunction
    
    virtual task run();
      Transaction trans;
      InternalBusTransaction tr;
      // While is enabled or stop = 0 or number of generated transactions not exceed limit
      while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin          
        trans = blueprint.copy;               // Copy from blueprint
        assert(trans.randomize());            // Randomize transaction
        
        // Generate transaction with "corner case" address
        assert(randomize());
        $cast(tr,trans);
        addr = base_addr;
        addr += ($urandom_range(1)) ? (offset)  : (0 - offset);
        addr += ($urandom_range(1)) ? (offset1) : (0 - offset1);
        tr.globalAddr =  addr;
        // Change length and data if needed
        if (tr.globalAddr[11:0] + tr.length > 13'h1000) begin
          tr.length = 13'h1000 - tr.globalAddr[11:0];
          if (tr.haveData()) begin
            tr.data = new[tr.length];
            for (int i=0; i < tr.data.size; i++)
              tr.data[i] = $urandom_range(0,255);
          end
        end
        
        trans.stream_id    = stream_id;       // Set stream id
        trans.scenario_id  = -1;              // Set default scenario
        trans.data_id      = data_id;         // Set instance count
        transMbx.put(trans);                  // Put transaction to mailbox
        data_id=data_id+1;                    // Increment instance counter
        
        //$write(".");
        #($dist_exponential(1,100)*1000);
        
      end;
      enabled = 0;
    endtask : run
    
  endclass
  
endpackage
