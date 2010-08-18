-- ib_switch_user.vhd: Internal Bus Switch for the User application core
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Puš <pus@liberouter.org>
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
use work.ib_pkg.all; -- Internal Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SWITCH_SYNTH is
port(
   IB_CLK               : in  std_logic;
   IB_RESET             : in  std_logic;

   PORT0_UP_DATA        : out std_logic_vector(63 downto 0);
   PORT0_UP_SOP_N       : out std_logic;
   PORT0_UP_EOP_N       : out std_logic;
   PORT0_UP_SRC_RDY_N   : out std_logic;
   PORT0_UP_DST_RDY_N   : in  std_logic;
   PORT0_DOWN_DATA      : in  std_logic_vector(63 downto 0);
   PORT0_DOWN_SOP_N     : in  std_logic;
   PORT0_DOWN_EOP_N     : in  std_logic;
   PORT0_DOWN_SRC_RDY_N : in  std_logic;
   PORT0_DOWN_DST_RDY_N : out std_logic;

   PORT1_UP_DATA        : in  std_logic_vector(63 downto 0);
   PORT1_UP_SOP_N       : in  std_logic;
   PORT1_UP_EOP_N       : in  std_logic;
   PORT1_UP_SRC_RDY_N   : in  std_logic;
   PORT1_UP_DST_RDY_N   : out std_logic;
   PORT1_DOWN_DATA      : out std_logic_vector(63 downto 0);
   PORT1_DOWN_SOP_N     : out std_logic;
   PORT1_DOWN_EOP_N     : out std_logic;
   PORT1_DOWN_SRC_RDY_N : out std_logic;
   PORT1_DOWN_DST_RDY_N : in  std_logic;

   PORT2_UP_DATA        : in  std_logic_vector(63 downto 0);
   PORT2_UP_SOP_N       : in  std_logic;
   PORT2_UP_EOP_N       : in  std_logic;
   PORT2_UP_SRC_RDY_N   : in  std_logic;
   PORT2_UP_DST_RDY_N   : out std_logic;
   PORT2_DOWN_DATA      : out std_logic_vector(63 downto 0);
   PORT2_DOWN_SOP_N     : out std_logic;
   PORT2_DOWN_EOP_N     : out std_logic;
   PORT2_DOWN_SRC_RDY_N : out std_logic;
   PORT2_DOWN_DST_RDY_N : in  std_logic
);
end entity IB_SWITCH_SYNTH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_USER_ARCH of IB_SWITCH_SYNTH is

   signal ibus0 : t_internal_bus64;
   signal ibus1 : t_internal_bus64;
   signal ibus2 : t_internal_bus64;

begin

   IB_SWITCH0_I: entity work.IB_SWITCH
   generic map(
      -- Data Width (64/128)
      DATA_WIDTH        => 64,
      -- Port 0 Address Space 
      SWITCH_BASE       => X"02000000",
	   SWITCH_LIMIT      => X"02000000", -- 0x200 0000 to 0x3FF FFFF
	   -- Port 1 Address Space
	   DOWNSTREAM0_BASE  => X"02000000",
	   DOWNSTREAM0_LIMIT => X"00300000", -- 0x200 0000 to 0x22F FFFF
	   -- Port 2 Address Space
	   DOWNSTREAM1_BASE  => X"02300000",
	   DOWNSTREAM1_LIMIT => X"01D00000"  -- 0x230 0000 to 0x3FF FFFF
	   )
	   port map(
	      -- Common Interface
	      IB_CLK      => IB_CLK,
	      IB_RESET    => IB_RESET,
	
	      PORT0       => ibus0,
	      PORT1       => ibus1,
	      PORT2       => ibus2
	   );
	
	   -- Upstream Port
	   PORT0_UP_DATA        <= ibus0.UP.DATA;
	   PORT0_UP_SOP_N       <= ibus0.UP.SOP_N;
	   PORT0_UP_EOP_N       <= ibus0.UP.EOP_N;
	   PORT0_UP_SRC_RDY_N   <= ibus0.UP.SRC_RDY_N;
	   ibus0.UP.DST_RDY_N   <= PORT0_UP_DST_RDY_N;
	   ibus0.DOWN.DATA      <= PORT0_DOWN_DATA;
	   ibus0.DOWN.SOP_N     <= PORT0_DOWN_SOP_N;
	   ibus0.DOWN.EOP_N     <= PORT0_DOWN_EOP_N;
	   ibus0.DOWN.SRC_RDY_N <= PORT0_DOWN_SRC_RDY_N;
	   PORT0_DOWN_DST_RDY_N <= ibus0.DOWN.DST_RDY_N;
	   -- Downstream Ports
	   ibus1.UP.DATA        <= PORT1_UP_DATA;
	   ibus1.UP.SOP_N       <= PORT1_UP_SOP_N;
	   ibus1.UP.EOP_N       <= PORT1_UP_EOP_N;
	   ibus1.UP.SRC_RDY_N   <= PORT1_UP_SRC_RDY_N;
	   PORT1_UP_DST_RDY_N   <= ibus1.UP.DST_RDY_N;
	   PORT1_DOWN_DATA      <= ibus1.DOWN.DATA;
	   PORT1_DOWN_SOP_N     <= ibus1.DOWN.SOP_N;
	   PORT1_DOWN_EOP_N     <= ibus1.DOWN.EOP_N;
	   PORT1_DOWN_SRC_RDY_N <= ibus1.DOWN.SRC_RDY_N;
	   ibus1.DOWN.DST_RDY_N <= PORT1_DOWN_DST_RDY_N;
	
	   ibus2.UP.DATA        <= PORT2_UP_DATA;
	   ibus2.UP.SOP_N       <= PORT2_UP_SOP_N;
	   ibus2.UP.EOP_N       <= PORT2_UP_EOP_N;
	   ibus2.UP.SRC_RDY_N   <= PORT2_UP_SRC_RDY_N;
	   PORT2_UP_DST_RDY_N   <= ibus2.UP.DST_RDY_N;
	   PORT2_DOWN_DATA      <= ibus2.DOWN.DATA;
	   PORT2_DOWN_SOP_N     <= ibus2.DOWN.SOP_N;
	   PORT2_DOWN_EOP_N     <= ibus2.DOWN.EOP_N;
	   PORT2_DOWN_SRC_RDY_N <= ibus2.DOWN.SRC_RDY_N;
	   ibus2.DOWN.DST_RDY_N <= PORT2_DOWN_DST_RDY_N;
	
	end architecture IB_SWITCH_USER_ARCH;
