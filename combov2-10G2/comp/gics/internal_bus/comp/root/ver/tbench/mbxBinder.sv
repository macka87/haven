/*
 * mbxBinder.sv: Mailbox Binder
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky  <kobiersky@liberouter.org>
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
 * $Id $
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- MailboxBinder Class
  // --------------------------------------------------------------------------
  class MailboxBinder;
  
    // -- Public Class Atributes --
    tTransMbx transMbx;
    tTransMbx inMbx[$];
    bit enabled;
    int activeMbx;

    //-------------------------------------------------------------------------
    function new(string inst, int stream_id = -1, tTransMbx transMbx = null);
      if (transMbx == null)  
        this.transMbx = new(1);          // Create own mailbox
      else
        this.transMbx = transMbx;        // Use created mailbox
      enabled         = 0;               // Disable generator by default
      activeMbx       = 0;               // Active Mailbox
    endfunction : new
    
    // -- Set Callbacks -------------------------------------------------------
    // Put callback object into List 
    function void setInputMailbox(tTransMbx mbx);
      this.inMbx.push_back(mbx);
    endfunction : setInputMailbox

    //-------------------------------------------------------------------------
    /*
     * Enable Mailbox Binder
     */
    task setEnabled();
      enabled = 1;
      fork
        run();
      join_none;
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
      Transaction to;
      int ok;
      int auxMbx;
      // While is enabled
      while (enabled) begin
        auxMbx = activeMbx; // Get most prioritized Mbx
        do begin
          ok = inMbx[auxMbx].try_get(to);
          if (ok == 0) begin
            if (auxMbx == inMbx.size-1)
              auxMbx = 0;
            else
              auxMbx = auxMbx+1;
          end
        end while (ok == 0 && auxMbx != activeMbx);

        if (ok) begin
          transMbx.put(to);
          if (activeMbx == inMbx.size-1)
            activeMbx = 0;
          else
            activeMbx = activeMbx+1;
          end
        else
          #1ns;
      end;
    endtask : run
  endclass : MailboxBinder
