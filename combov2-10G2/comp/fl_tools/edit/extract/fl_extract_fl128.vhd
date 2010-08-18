-- fl_extract_fl128.vhd:  FrameLink Extract generic wrapper
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- library with t_flxx data types
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_EXTRACT_FL128 is
   generic(
      PIPELINE_EN  : boolean:= false; -- Enable registers on output fl interface

      -- Header / Footer data present
      PACKET_NO    : integer; -- Part of Frame where the field is extracted

      -- Extract option
      OFFSET       : integer; -- Start extracting on specified offset
      SIZE         : integer;  -- Size of "Extracted field" in Bytes
      
      -- FrameLink frame parametrs
      PARTS        : integer := 4;     -- number of parts in FL frame
      LENGTH       : integer := 2048  -- maximal length of FL frame part
      );
   port(
      CLK          : in std_logic;
      RESET        : in std_logic;

      EXT_DATA     : out std_logic_vector(SIZE*8-1 downto 0);
      EXT_DATA_VLD : out std_logic;

      -- Input Interface
      RX           : inout t_fl128;

      -- Output Interface
      TX           : inout t_fl128
   );
end entity FL_EXTRACT_FL128;

architecture full of FL_EXTRACT_FL128 is
begin
FL_EXTRACT_ENTITY: entity work.FL_EXTRACT 
   generic map(
      -- Frame link width
      DATA_WIDTH=>128,
      PIPELINE_EN=>PIPELINE_EN, -- Enable registers on output fl interface

      -- Header / Footer data present
      PACKET_NO=>PACKET_NO, -- Part of Frame where the field is extracted

      -- Extract option
      OFFSET=>OFFSET, -- Start extracting on specified offset
      SIZE=>SIZE,  -- Size of "Extracted field" in Bytes
      
      PARTS => PARTS,
      LENGTH => LENGTH
      )
   port map(
      CLK=>CLK,
      RESET=>RESET,

      EXT_DATA=>EXT_DATA,
      EXT_DATA_VLD=>EXT_DATA_VLD,

      -- Input Interface
      RX_DATA=>RX.DATA,
      RX_REM=>RX.DREM,
      RX_SRC_RDY_N=>RX.SRC_RDY_N,
      RX_DST_RDY_N=>RX.DST_RDY_N,
      RX_SOP_N=>RX.SOP_N,
      RX_EOP_N=>RX.EOP_N,
      RX_SOF_N=>RX.SOF_N,
      RX_EOF_N=>RX.EOF_N,

      -- Output Interface
      TX_DATA=>TX.DATA,
      TX_REM=>TX.DREM,
      TX_SRC_RDY_N=>TX.SRC_RDY_N,
      TX_DST_RDY_N=>TX.DST_RDY_N,
      TX_SOP_N=>TX.SOP_N,
      TX_EOP_N=>TX.EOP_N,
      TX_SOF_N=>TX.SOF_N,
      TX_EOF_N=>TX.EOF_N
   );
end architecture full;
