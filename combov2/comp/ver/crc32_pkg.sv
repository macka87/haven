/*
 * \file crc32_pkg.sv
 * \brief CRC32 package
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
 * $Id: crc32_pkg.sv 12754 2010-02-12 01:51:30Z xsanta06 $
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ---------------------------------------------------------------------------- 

package crc32_pkg;

  bit [31:0] crcTable[] = '{
    32'h4DBDF21C, 32'h500AE278, 32'h76D3D2D4, 32'h6B64C2B0,
    32'h3B61B38C, 32'h26D6A3E8, 32'h000F9344, 32'h1DB88320,
    32'hA005713C, 32'hBDB26158, 32'h9B6B51F4, 32'h86DC4190,
    32'hD6D930AC, 32'hCB6E20C8, 32'hEDB71064, 32'hF0000000
      }; 

  // -------------------------------------------------------------------------
  //! CRC Compute
  /*! Compute CRC of input data. 
   *
   * \param data - input data which CRC we need
   * \return - CRC value
   */
  function bit[31:0] crcCompute (byte unsigned data[]);
    bit [31:0] crc;

    crc = 0;

    for (int i=0; i < data.size; i++) begin
      // lower nibble
      crc = (crc >> 4) ^ crcTable[(crc ^ (data[i] >> 0)) & 'h0F];
      // upper nibble
      crc = (crc >> 4) ^ crcTable[(crc ^ (data[i] >> 4)) & 'h0F];
    end

    return (crc & 32'hFFFFFFFF);
  endfunction: crcCompute

endpackage: crc32_pkg;
