-- fl_distributor_ent.vhd: FrameLink 1-4 switch entity.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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
entity fl_distributor is
   generic (
      -- FrameLink data width
      DATA_WIDTH : integer := 64;

      -- count of output interfaces, MUST be 2^n and greater than one
      INTERFACES_COUNT : integer := 8;

      -- default interface that is used when the interface
      -- number doesn't come in the frame
      DEFAULT_INTERFACE : integer := 0;

      -- offset from the start of the part (in bits)
      -- where the interface number (INUM) is placed
      INUM_OFFSET : integer := 113;

      -- number of parts in every frame
      PARTS : integer := 2
   );
   port (
      CLK          : in std_logic;
      RESET        : in std_logic;

      -- Write interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;

      -- Read interfaces
      TX_DATA     : out std_logic_vector(INTERFACES_COUNT*DATA_WIDTH-1 downto 0);
      TX_REM      : out std_logic_vector(INTERFACES_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N: out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_DST_RDY_N: in  std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOP_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_SOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0);
      TX_EOF_N    : out std_logic_vector(INTERFACES_COUNT-1 downto 0)
   );
end entity fl_distributor;

