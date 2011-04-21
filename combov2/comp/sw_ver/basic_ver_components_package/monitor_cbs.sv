/*
 * monitorCbs.sv: Monitor Callbacks
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
 *            Petr Kobiersky <kobiersky@liberouter.org>
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
 * $Id$
 *
 * TODO:
 *
 */

  // --------------------------------------------------------------------------
  // -- Frame Link Monitor Callbacks
  // --------------------------------------------------------------------------
  /* This is a abstract class for creating objects which get benefits from
   * function callback. This object can be used with Monitor
   * class. Inheritence from this basic class is neaded for functionality.
   */
  class MonitorCbs;
  // -- Class Methods --

    // ------------------------------------------------------------------------
    // Function is called before post_rx is called (modification of transaction)
    virtual task pre_rx(ref Transaction transaction, string inst);
      // By default, callback does nothing
    endtask
    
    // ------------------------------------------------------------------------
    // Function is called after is transaction received (scoreboard)
    virtual task post_rx(Transaction transaction, string inst);
      // By default, callback does nothing
    endtask
  
  endclass : MonitorCbs

