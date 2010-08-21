--
-- mi_splitter.vhd: MI Splitter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ---------------------------------------------------------------------------- 

entity MI_SPLITTER_PLUS is
   generic(
      -- Data width
      DATA_WIDTH    : integer := 32;
      -- Number of output ports
      ITEMS         : integer;
      -- Bits of address that should been compared
      ADDR_CMP_MASK : std_logic_vector(31 downto 0) := X"FFFFFFFF";
      -- Bases of address spaces (base of port0 is 0x00000000)
      PORT1_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT2_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT3_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT4_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT5_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT6_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      PORT7_BASE    : std_logic_vector(31 downto 0) := X"00000000";
      -- Input pipeline
      PIPE          : boolean := false;
      PIPE_OUTREG   : boolean := false
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector(31 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*32-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)
      
   );
end entity MI_SPLITTER_PLUS;

