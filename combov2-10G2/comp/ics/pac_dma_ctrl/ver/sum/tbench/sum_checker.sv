/* \file sum_checker.sv
 * \brief Checker for Status Update Manager
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
 *
 *
 * TODO:
 *
 */

import sv_common_pkg::*;

  // --------------------------------------------------------------------------
  // -- Packet Counter
  // -------------------------------------------------------------------------- 
  /*!
   * \brief Packet Counter
   * 
   * This class is responsible for creating packet counter for each flow.
   * It also prints counter.   
   *    
   * \param pFlows - count of flows
   */
  class PacketCounter;
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Packet Counter identification
    string inst;
    //! Counter
    int unsigned counter;
    int unsigned removedCount;
    
    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * It initializes counter.
     * 
     * \param inst - packet identification
     * \param initValue - counter initialization value
     */
    function new (string inst="", int unsigned initValue = 0);
      this.inst = inst;
    
      this.counter = initValue; 

    endfunction

    // -- Get Value -----------------------------------------------------------
    //! Get value
    /*!
     * Return counter value.
     * 
     */
    function int unsigned getValue();
      return counter;
    endfunction

    // -- Increment -----------------------------------------------------------
    //! Increment
    /*!
     * Increment counter value.
     * 
     */
    function void increment();
      counter++;
    endfunction

    // -- Removed -------------------------------------------------------------
    //! Removed  
    /*!
     * Notice removed counter.
     * 
     */
    function void removed(int unsigned value);
      removedCount = value;
    endfunction

   // -- Display -------------------------------------------------------------
    //! Display 
    /*!
     * It prints counter status
     * 
     */
    task display();
      $write("------------------------------------------------------------\n");
      $write("-- %s\n",inst);
      $write("------------------------------------------------------------\n");
      $write("Left: %0d\n",counter-removedCount);
      $write("Expected: %0d\n",counter);
      $write("Received: %0d\n",removedCount);
      $write("------------------------------------------------------------\n");
    endtask
  
  endclass : PacketCounter

  // --------------------------------------------------------------------------
  // -- SUM Driver Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Status Update Manager Driver Callbacks
   * 
   * This class is responsible incrementing counters of transmitted packets  
   *    
   * \param pFlows - count of flows
   */
  
  class CheckerDriverCbs #(int pFlows=2)extends DriverCbs;

    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Packet Counters
    PacketCounter packetCounter[];

    // -------------------
    // -- Class Methods --
    // -------------------

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param packetCounter - Packet counters
     */
    function new (PacketCounter packetCounter[]);
      this.packetCounter = packetCounter;
    endfunction
    
    // -- Pre_tx --------------------------------------------------------------
    //! Pre_tx 
    /*!
     * Function is called before transaction is sended.
     */
    virtual task pre_tx(ref Transaction transaction, string inst);
    endtask
    
    // -- Post_tx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is sended. It adds transaction into
     * correct transaction table - depends on witch driver sends transaction               
     * 
     * \param transaction - transaction 
     * \param inst - driver identifier         
     */
    
    virtual task post_tx(Transaction transaction, string inst);
      StatusUpdateTransaction tr;

      $cast(tr, transaction);

      packetCounter[tr.address].increment();
    endtask

   endclass : CheckerDriverCbs


  // --------------------------------------------------------------------------
  // -- SUM Checker Callbacks
  // --------------------------------------------------------------------------
  /*!
   * \brief Status Update Manager Checker Callbacks
   * 
   * This class is responsible for comparing packet counters status.
   *    
   * \param pFlows - count of flows
   */
  
  class CheckerMonitorCbs #(int pFlows=1);
    
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Checker identification
    string inst;
    //! Packet Counters
    PacketCounter packetCounter[];
    
    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * \param packetCounter - Packet counters
     */
    function new (PacketCounter packetCounter[]);
      this.packetCounter = packetCounter;
    endfunction
    
    // -- Post_rx -------------------------------------------------------------
    //! Post_tx 
    /*!
     * Function is called after transaction is received. It checks correct
     * transaction table for the same transaction. If they match, transaction is
     * removed, otherwise error is reporting.                         
     * 
     * \param transaction - transaction 
     * \param inst - monitor identifier         
     */
     
    virtual task post_rx(bit[31:0] value = 0, int flow);

//      $write("Expected %0d: %0d\n", flow, packetCounter[flow].getValue());
//      $write("Received %0d: %0d\n", flow, value);

      if (value != packetCounter[flow].getValue() &&
          value != packetCounter[flow].getValue()-1) begin
        $write("Received incorrect transmitted packet count for flow %0d\n",
                flow);
        $timeformat(-9, 3, " ns", 8);
        $write("Time: %t\n", $time);
        packetCounter[flow].display();
        $stop;
      end
      else packetCounter[flow].removed(value);
    endtask
 
  endclass : CheckerMonitorCbs


  // --------------------------------------------------------------------------
  // -- SUM Checker
  // -------------------------------------------------------------------------- 
  /*!
   * \brief Status Update Manager Checker
   * 
   * This class is responsible for creating transmitted packet counter and 
   * monitor and driver callback classes. It also prints counter.   
   *    
   * \param pFlows - count of flows
   */
  class SumChecker #(int pFlows=2);
    // ---------------------
    // -- Class Variables --
    // ---------------------
    //! Checker identification
    string inst;
    //! Array of transmitted packet counters
    PacketCounter packetCounter[];
    
    //! Monitor callback
    CheckerMonitorCbs #(pFlows) monitorCbs;
    //! Driver callback
    CheckerDriverCbs  #(pFlows) driverCbs;

    // -- Constructor ---------------------------------------------------------
    //! Constructor 
    /*!
     * It creates monitor and driver callbacks and packet counter for each 
     * flow.
     * 
     * \param inst - checker identification
     */
    function new (string inst="");
      this.inst = inst;
    
      this.packetCounter = new[pFlows]; 

      foreach(packetCounter[i]) begin
        string counterLabel;

        $swrite(counterLabel,"TX %0d",i);
        packetCounter[i] = new(counterLabel);
      end  

      this.monitorCbs = new(packetCounter);
      this.driverCbs  = new(packetCounter);
    endfunction

    // -- Display -------------------------------------------------------------
    //! Display 
    /*!
     * It prints Packet Counters
     * 
     */
    task display();
      $write("------------------------------------------------------------\n");
      $write("-- %s\n",inst);
      $write("------------------------------------------------------------\n");
      foreach (packetCounter[i])
        packetCounter[i].display();
      $write("------------------------------------------------------------\n");
    endtask
  
  endclass : SumChecker

