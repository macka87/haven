-- simple_marker_ent.vhd: Entity of simple FrameLink marker
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SIMPLE_FL_MARKER is
   generic(
      -- Frame link width
      DATA_WIDTH   : integer := 32;

      -- number of framelink parts
      PARTS        : integer := 2;

      -- which part will be marked or in which part will be inserted data
      MARK_PART    : integer := 0;

      -- mark options
      OFFSET       : integer := 0; -- "Mark" position - distance in bytes from start
                                   -- part

      MARK_SIZE    : integer := 4; -- Size of "Mark" in Bytes

      -- architecture switch (false = ReWrite, true = Insert)
      INSERT       : boolean := false
   );
   port (
      CLK          : in  std_logic; -- clock
      RST          : in  std_logic; -- reset

      -- mark input
      MARK         : in  std_logic_vector(MARK_SIZE*8-1 downto 0);

      -- valid mark value
      MARK_VALID   : in  std_logic;
      -- mark was placed, next mark expected
      MARK_NEXT    : out std_logic;

      -- Framelink RX interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;

      -- Framelink TX interface
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in std_logic
   );
end entity SIMPLE_FL_MARKER;
