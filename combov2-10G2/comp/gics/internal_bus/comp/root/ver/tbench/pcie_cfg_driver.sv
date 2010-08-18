//
// pcie_driver_pkg.sv: PCIe Driver
// Copyright (C) 2007 CESNET
// Author(s): Tomas Malek <tomalek@liberouter.org>
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in
//    the documentation and/or other materials provided with the
//    distribution.
// 3. Neither the name of the Company nor the names of its contributors
//    may be used to endorse or promote products derived from this
//    software without specific prior written permission.
//
// This software is provided ``as is'', and any express or implied
// warranties, including, but not limited to, the implied warranties of
// merchantability and fitness for a particular purpose are disclaimed.
// In no event shall the company or contributors be liable for any
// direct, indirect, incidental, special, exemplary, or consequential
// damages (including, but not limited to, procurement of substitute
// goods or services; loss of use, data, or profits; or business
// interruption) however caused and on any theory of liability, whether
// in contract, strict liability, or tort (including negligence or
// otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// $Id: pcie_cfg_driver.sv 4393 2008-08-05 21:28:10Z xkobie00 $
//

  // --------------------------------------------------------------------------
  // -- PCI Express Driver Class
  // --------------------------------------------------------------------------
  /* This class is responsible for generating signals to PCIe
   * interface. Transactions are received by 'transMbx'(Mailbox) property.
   * Unit must be enabled by "setEnable()" function call. Generation can be
   * stoped by "setDisable()" function call. You can send your custom
   * transcaction by calling "sendTransaction" function.
   */
  class PcieCfgDriver;
    // -- Private Class Atributes --
    string    inst;                             // Driver identification
    bit       enabled;                          // Driver is enabled
    virtual   iPcieCfg.driver pcieCfg;          // PCIe configuration interface
   
    logic	[7:0]  bus_number = 0;
    logic	[4:0]  device_number = 0;
    logic	[2:0]  function_number = 0;
    logic [2:0]  maxReadRequestSize = 3'b101;
    logic [2:0]  maxPayloadSize = 3'b101;
 
    // -- Public Class Methods --

    // -- Constructor ---------------------------------------------------------
    // Create driver object 
    function new ( string                  inst,
                   virtual iPcieCfg.driver pcieCfg);
      this.inst        = inst;         // Store driver identifier
      this.pcieCfg     = pcieCfg;      // Store pointer interface       

      // Setting values for PCIe configuration interface
      this.pcieCfg.cb_driver.DO                  <= 0;
      this.pcieCfg.cb_driver.RD_WR_DONE_N        <= 0;
      this.pcieCfg.cb_driver.INTERRUPT_RDY_N     <= 0;
      this.pcieCfg.cb_driver.INTERRUPT_MMENABLE  <= 0;
      this.pcieCfg.cb_driver.INTERRUPT_MSIENABLE <= 0;
      this.pcieCfg.cb_driver.INTERRUPT_DO        <= 0;
      this.pcieCfg.cb_driver.TO_TURNOFF_N        <= 0;
      this.pcieCfg.cb_driver.BUS_NUMBER          <= bus_number;
      this.pcieCfg.cb_driver.DEVICE_NUMBER       <= device_number;
      this.pcieCfg.cb_driver.FUNCTION_NUMBER     <= function_number;
      this.pcieCfg.cb_driver.STATUS              <= 0;
      this.pcieCfg.cb_driver.COMMAND             <= 0;
      this.pcieCfg.cb_driver.DSTATUS             <= 0;
      this.pcieCfg.cb_driver.DCOMMAND            <= {1'b0, maxReadRequestSize, 4'b0000, maxPayloadSize, 5'b00000};
      this.pcieCfg.cb_driver.LSTATUS             <= 0;
      this.pcieCfg.cb_driver.LCOMMAND            <= 0;
      this.pcieCfg.cb_driver.PCIE_LINK_STATE_N   <= 0;
      this.pcieCfg.cb_driver.ERR_CPL_RDY_N       <= 0;
   endfunction: new

    // -- Set Maximal Payload Size --------------------------------------------
    // Set Max. size of packet payload, See more p.342 of PCIe specification
    function void setMaxPayloadSize(integer size);
      case (size)
        128: 
          maxPayloadSize = 3'b000;
        256: 
          maxPayloadSize = 3'b001;
        512: 
          maxPayloadSize = 3'b010;
        1024: 
          maxPayloadSize = 3'b011;
        2048: 
          maxPayloadSize = 3'b100;
        4096: 
          maxPayloadSize = 3'b101;          
        default
          $write("Unknown Max Payload Size");
      endcase;
      this.pcieCfg.cb_driver.DCOMMAND  <= {1'b0, maxReadRequestSize, 4'b0000, maxPayloadSize, 5'b00000};
    endfunction : setMaxPayloadSize

    // -- Set Maximal Read Request size ---------------------------------------
    // Set Max. read request size of packet payload, See more p.375 of PCIe specification
    function void setMaxReadRequestSize(integer size);
      case (size)
        128: 
          maxReadRequestSize = 3'b000;
        256: 
          maxReadRequestSize = 3'b001;
        512: 
          maxReadRequestSize = 3'b010;
        1024: 
          maxReadRequestSize = 3'b011;
        2048: 
          maxReadRequestSize = 3'b100;
        4096: 
          maxReadRequestSize = 3'b101;          
        default
          $write("Unknown Max Read Request Size");
      endcase;
      this.pcieCfg.cb_driver.DCOMMAND  <= {1'b0, maxReadRequestSize, 4'b0000, maxPayloadSize, 5'b00000};
    endfunction : setMaxReadRequestSize

    // -- Set Bridge Identification -------------------------------------------
    function void setBridgeId(logic	[7:0] bus_number, logic	[4:0] device_number, logic	[2:0] function_number);
      this.bus_number      = bus_number;
      this.device_number   = device_number;
      this.function_number = function_number;
      this.pcieCfg.cb_driver.BUS_NUMBER          <= bus_number;
      this.pcieCfg.cb_driver.DEVICE_NUMBER       <= device_number;
      this.pcieCfg.cb_driver.FUNCTION_NUMBER     <= function_number;
    endfunction : setBridgeId

endclass : PcieCfgDriver

