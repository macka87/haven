/* *****************************************************************************
 * Project Name: Software Framework for Functional Verification 
 * File Name:    MI32 Interface
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         24.4.2011 
 * ************************************************************************** */
 

/*
 *  MI32 Interface
 */
interface iMi32 (input logic CLK, RESET);  
  logic [31:0] ADDR  = 0;  // ADDRess
  logic [31:0] DWR   = 0;  // Data to be WRitten
  logic [31:0] DRD;        // Data to be ReaD
  logic [3:0] BE     = 0;  // Byte Enable
  logic RD           = 0;  // ReaD request
  logic WR           = 0;  // WRite request
  logic ARDY;              // Address ReaDY
  logic DRDY;              // Data ReaDY
  
  clocking cb @(posedge CLK);
    input  ARDY, DRDY, DRD;
    output ADDR, DWR, BE, RD, WR;  
  endclocking: cb;

  clocking monitor_cb @(posedge CLK);
    input ADDR, DWR, DRD, BE, RD, WR, ARDY, DRDY;
  endclocking: monitor_cb;

  /*
   * Receive Modport
   */
   modport dut (input  ADDR,
                input  DWR,
                input  BE,
                input  RD,
                input  WR,
                output ARDY,
                output DRDY,
                output DRD);
  
  // Driver Modport
  modport tb (clocking cb);

  // Monitor Modport
  modport monitor (clocking monitor_cb);
  
 /*
  * Interface properties/assertions
  */
  
  // -- While RESET RD inactive ----------------------------------------
  // RD may be active only if RESET is inactive. 
  property RESETR;
     @(posedge CLK) (RESET)|->(not RD); 
  endproperty   
  
  assert property (RESETR)
     else $error("RD is active during reset.");

  // -- While RESET WR inactive ----------------------------------------
  // WR may be active only if RESET is inactive. 
  property RESETW;
     @(posedge CLK) (RESET)|->(not WR); 
  endproperty   
  
  assert property (RESETW)
     else $error("WR is active during reset.");
  
  // -- ARDY together with RD or WR -------------------------------------
  // ARDY must be active together with RD or WR.
  property ARDYWRRD;
     @(posedge CLK) (ARDY)|->(WR || RD); 
  endproperty
  
  assert property (ARDYWRRD)
     else $error("ARDY and WR or RD signals are not active at the same cycle.");
     
  // -- WR never together with RD ---------------------------------------
  // WR can not be active together with RD.
  property RDnottogetherWR;
     @(posedge CLK) (RD)|->(!WR); 
  endproperty
  
  assert property (RDnottogetherWR)
     else $error("RD and WR signals can not be active at the same cycle.");   
endinterface : iMi32
