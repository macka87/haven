-- marker_ent.vhd: FrameLink header / footer marker entity.
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Trs <trsm1@liberouter.org>
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
entity FL_MARKER is
   generic(
      -- Frame link width
      DATA_WIDTH   : integer := 32;
      -- Header / Footer data present
      HEADER       : boolean := true;
      FOOTER       : boolean := true;

      -- Mark options
      OFFSET       : integer := 4; -- "Mark" position in FL Header in Bytes
      SIZE         : integer := 1; -- Size of "Mark" in Bytes
      -- Add "mark" to header or footer (only one can be choice)
      MARK_HDR     : boolean := true;
      MARK_FTR     : boolean := false;
      -- architecture switch (false = ReWrite, true = Insert)
      INSERT       : boolean := false

   );
   port(
      CLK          : in std_logic;
      RESET        : in std_logic;

      MARK         : in  std_logic_vector(SIZE*8-1 downto 0);
      MARK_NEXT    : out std_logic;

      -- Write interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;

      -- Read interface
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in  std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic
   );
end entity FL_MARKER;
