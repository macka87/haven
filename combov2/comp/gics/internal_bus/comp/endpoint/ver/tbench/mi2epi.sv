/*
 * mi2epi.sv: MI to Endpoint interface converter
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
 * $Id: mi2epi.sv 8956 2009-06-24 21:16:49Z washek $
 *
 * TODO:
 *
 */
 
// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------

module MI2EPI #(int DATA_WIDTH = 64, int ADDR_WIDTH = 32) (
  iMI.slave            MI,
  iIbEndpointWrite.ep  WR,
  iIbEndpointRead.ep   RD
  );
  
  always begin
    WR.ADDR    <= MI.ADDR;
    WR.DATA    <= MI.DWR;
    WR.BE      <= MI.BE;
    WR.REQ     <= MI.WR;
    
    RD.ADDR    <= MI.ADDR;
    RD.BE      <= MI.BE;
    RD.REQ     <= MI.RD;
    RD.DST_RDY <= 1'b1;
    
    MI.ARDY    <= WR.RDY || RD.ARDY_ACCEPT;
    MI.DRD     <= RD.DATA;
    MI.DRDY    <= RD.SRC_RDY;
  end
    
  initial begin
    WR.LENGTH <= 'x;
    WR.SOF    <= 'x;
    WR.EOF    <= 'x;
    
    RD.LENGTH <= 'x;
    RD.SOF    <= 'x;
    RD.EOF    <= 'x;
  end
  
endmodule
