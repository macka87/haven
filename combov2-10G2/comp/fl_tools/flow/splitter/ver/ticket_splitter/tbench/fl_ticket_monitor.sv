/*
 * fl_ticket_monitor.sv: FrameLink Ticket Monitor
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
 * $Id: fl_ticket_monitor.sv 10588 2009-08-21 09:02:15Z xsanta06 $
 *
 * TODO:
 *
 */
 
 
  // --------------------------------------------------------------------------
  // -- FrameLink Ticket Monitor Class
  // --------------------------------------------------------------------------
  /* This class is responsible for creating transaction objects from 
   * FrameLink and Output ticket interface signals. After is transaction 
   * received it is sended by callback to processing units (typicaly scoreboard)
   * Unit must be enabled by "setEnable()" function call. Monitoring can be 
   * stoped by "setDisable()" function call.
   */
  class FrameLinkTicketMonitor #(int pDataWidth=32, int pDremWidth=2, 
                                 int pTicketWidth = 8)
                            extends FrameLinkMonitor #(pDataWidth, pDremWidth);
    
    // -- Private Class Atributes --
    bit     ticketQue[$][pTicketWidth];    // Ticket queue
    virtual iControl.out_tb #(pTicketWidth) ctrl;
    
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    function new ( string inst,
                   virtual iFrameLinkTx.monitor #(pDataWidth,pDremWidth) fl,
                   virtual iControl.out_tb #(pTicketWidth) ctrl
                   );
      super.new(inst, fl);

      this.ctrl        = ctrl;        // Store pointer interface 
      
      this.ctrl.out_cb.CTRL_DATA_OUT_VLD  <= 0;
    endfunction

    // -- Enable Monitor ------------------------------------------------------
    // Enable monitor and runs monitor process
    task setEnabled();
      enabled = 1; // Monitor Enabling
      fork         
        run();           // Creating monitor subprocess
        receiveTicket(); // Creating ticket receiving subprocess
      join_none;   // Don't wait for ending
    endtask : setEnabled
        
    // -- Disable Monitor -----------------------------------------------------
    // Disable monitor
    task setDisabled();
      enabled = 0; // Disable monitor, after receiving last transaction
    endtask : setDisabled 
    
    // -- Run Monitor ---------------------------------------------------------
    // Receive transactions and send them for processing by call back
    task run();
      FrameLinkTransaction transaction; 
      FrameLinkTicketTransaction trans; 
      Transaction tr;

      while (enabled) begin              // Repeat in forewer loop
        trans= new;                      // Create new transaction object
        $cast(transaction, trans);
        $cast(tr, transaction);

        // Call transaction preprocesing, if is available
        foreach (cbs[i]) cbs[i].pre_rx(tr, inst);       

        // Receive Transaction
        receiveTransaction(transaction); // Receive Transaction
        
        // Add ticket into transaction
        addTicket(trans);
//        trans.display(inst);
        
        // Necessary for not calling callback after monitor disabling
        if (!enabled) break;

        #(0); // Necessary for not calling callback before driver
        
        // Call transaction postprocesing, if is available
        foreach (cbs[i]) cbs[i].post_rx(tr, inst);

        // Monitor received transaction and is not busy
        busy = 0;
      end
    endtask : run
    
    // -- Add Ticket ----------------------------------------------------------
    // Add ticket into transaction
    task addTicket(inout FrameLinkTicketTransaction tr);
      // Wait for ticket
      while (ticketQue.size == 0) @(ctrl.out_cb);

      tr.ticketData = ticketQue.pop_front();
    endtask : addTicket 
    
    // -- Receive Ticket ------------------------------------------------------
    // Receive ticket from ctrl interface
    task receiveTicket();
      logic [pTicketWidth-1:0] aux;
      bit ticket[pTicketWidth];

      while (enabled) begin
        // Wait for ticket data valid
        waitForCtrlDataOutVld();

        // Receive ticket
        for (int i=0; i<pTicketWidth; i++)
          ticket[i] = ctrl.out_cb.CTRL_DATA_OUT[i];
        ctrl.out_cb.CTRL_DATA_OUT_RQ <= 1;
        @(ctrl.out_cb);
        ctrl.out_cb.CTRL_DATA_OUT_RQ <= 0;

        // Add ticket to queue
        ticketQue.push_back(ticket);  
      end

    endtask : receiveTicket

    // -- Wait for ticket data valid ------------------------------------------
    // Waits for CTRL_DATA_OUT_VLD
    task waitForCtrlDataOutVld();
      while (!ctrl.out_cb.CTRL_DATA_OUT_VLD) @(ctrl.out_cb);
    endtask : waitForCtrlDataOutVld
    
  endclass : FrameLinkTicketMonitor    
