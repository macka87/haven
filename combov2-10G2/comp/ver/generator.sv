/*
 * generator.sv: Generator class package
 * Copyright (C) 2007 CESNET
 * Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
 *            Petr Kobiersky  <kobiersky@liberouter.org>
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
 * $Id: generator.sv 10384 2009-08-14 05:30:49Z xsanta06 $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Generator Class
  // --------------------------------------------------------------------------
  class Generator;
  
    // -- Public Class Atributes --
 
    //-------------------------------------------------------------------------
    /*
     * Internal mailbox is used only when no mailbox is specified in the
     * constructor.
     */
    tTransMbx transMbx;

    //-------------------------------------------------------------------------
    /*
     * The generator will stop after the specified number of object
     * instances has been generated and consumed by the output channel.
     * The generator must be reset before it can be restarted. If the
     * value of this property is 0, the generator will not stop on
     * its own.
     */
    int unsigned stop_after_n_insts = 0;
    
    //-------------------------------------------------------------------------
    /*
     * Transaction or data descriptor instance that is repeatedly
     * randomized to create the random content of the output descriptor
     * stream. The individual instances of the output stream are copied
     * from this instance, after randomization, using the
     * Transaction::copy() method. stream_id property of this instance is
     * set to the generator’s stream identifier before each randomization.
     * The Transaction::data_id property of this instance is also set
     * before each randomization. It will be reset to 0 when the generator
     * is reset and after the specified maximum number of instances has
     * been generated.
     */
    Transaction blueprint;

    bit enabled; 

    // -- Protected Class Atributes
    protected int stream_id;
    
    protected int scenario_id;
    
    protected int data_id;
    
    
    // -- Public Class Methods
    
    //-------------------------------------------------------------------------
    /*
     * Creates a new instance of the generator class with the specified
     * instance name and optional stream identifier. The generator can
     * be optionally connected to the specified output channel(mailbox).
     * If no output channel instance is specified, one will be created
     * internally in the out_chan property.
     */
    function new(string inst, int stream_id = -1, tTransMbx transMbx = null);
      if (transMbx == null)  
        this.transMbx = new(1);             // Create own mailbox
      else
        this.transMbx = transMbx;        // Use created mailbox
    
      enabled         = 0;               // Disable generator by default
      blueprint       = null;            // Null the blueprint transaction
      stream_id       = stream_id;       // Set stream id
      scenario_id     = -1;              // Set default scenario
      data_id         = 0;               // Set default data identifier
    endfunction : new
    
    //-------------------------------------------------------------------------
    /*
     * Enable generator for creating n Instances.
     */
    task setEnabled(int unsigned nInst=32'hFFFFFFFF);
      enabled = 1;
      stop_after_n_insts = nInst;
      data_id = 0;
      if ( blueprint != null) begin
        fork
          run();
        join_none;
        end
      else
        $write("The blueprint transaction in generator must be set\n");
    endtask : setEnabled
    
    //-------------------------------------------------------------------------
    /*
     * Disable generator immediately.
     */
    task setDisabled();
      this.enabled = 0;
    endtask : setDisabled
    

    //-------------------------------------------------------------------------
    virtual task run();
      Transaction trans;
      // While is enabled or stop = 0 or number of generated transactions not exceed limit
      while (enabled && (data_id < stop_after_n_insts || stop_after_n_insts == 0)) begin          
        trans = blueprint.copy;               // Copy from blueprint
        trans.stream_id    = stream_id;       // Set stream id
        trans.scenario_id  = -1;              // Set default scenario
        trans.data_id      = data_id;         // Set instance count
        assert(trans.randomize);              // Randomize transaction
//        trans.display("generator");
        transMbx.put(trans);                  // Put transaction to mailbox
        data_id=data_id+1;                    // Increment instance counter
      end;
      enabled = 0;
    endtask : run
    
  endclass : Generator

