--
-- ib_switch.vhd: Internal Bus Switch
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
entity IB_SWITCH is
   generic(
      -- Data Width (64/128)
      DATA_WIDTH        : integer:=64;
      -- Port 0 Address Space 
      SWITCH_BASE       : std_logic_vector(31 downto 0):=X"00000000";
      SWITCH_LIMIT      : std_logic_vector(31 downto 0):=X"33333333";
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  : std_logic_vector(31 downto 0):=X"00000000";
      DOWNSTREAM0_LIMIT : std_logic_vector(31 downto 0):=X"11111111";
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  : std_logic_vector(31 downto 0):=X"11111111"; 
      DOWNSTREAM1_LIMIT : std_logic_vector(31 downto 0):=X"22222222"
   );
   
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      IB_RESET      : in std_logic;
      -- Upstream Port
      PORT0         : inout t_internal_bus64;
      -- Downstream Ports
      PORT1         : inout t_internal_bus64;
      PORT2         : inout t_internal_bus64
   );
end entity IB_SWITCH;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_ARCH of IB_SWITCH is
   
      signal reset_pipe : std_logic;
      attribute equivalent_register_removal : string;
      attribute equivalent_register_removal of reset_pipe : signal is "no";
begin

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(IB_RESET, IB_CLK)
   begin
      if IB_CLK'event and IB_CLK = '1' then
         reset_pipe  <= IB_RESET;
      end if;
end process;

-- -----------------------Portmaping of tested component-----------------------
IB_SWITCH_CORE_U: entity work.IB_SWITCH_CORE
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH        => DATA_WIDTH,       
      SWITCH_BASE       => SWITCH_BASE,
      SWITCH_LIMIT      => SWITCH_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  => DOWNSTREAM0_BASE,
      DOWNSTREAM0_LIMIT => DOWNSTREAM0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  => DOWNSTREAM1_BASE,
      DOWNSTREAM1_LIMIT => DOWNSTREAM1_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK                => IB_CLK,
      IB_RESET              => reset_pipe,

      PORT0_DOWN_DATA       => PORT0.DOWN.DATA,
      PORT0_DOWN_SOP_N      => PORT0.DOWN.SOP_N,
      PORT0_DOWN_EOP_N      => PORT0.DOWN.EOP_N,
      PORT0_DOWN_SRC_RDY_N  => PORT0.DOWN.SRC_RDY_N,
      PORT0_DOWN_DST_RDY_N  => PORT0.DOWN.DST_RDY_N,
      PORT0_UP_DATA         => PORT0.UP.DATA,
      PORT0_UP_SOP_N        => PORT0.UP.SOP_N,
      PORT0_UP_EOP_N        => PORT0.UP.EOP_N,
      PORT0_UP_SRC_RDY_N    => PORT0.UP.SRC_RDY_N,
      PORT0_UP_DST_RDY_N     => PORT0.UP.DST_RDY_N,

      PORT1_DOWN_DATA       => PORT1.DOWN.DATA,
      PORT1_DOWN_SOP_N      => PORT1.DOWN.SOP_N,
      PORT1_DOWN_EOP_N      => PORT1.DOWN.EOP_N,
      PORT1_DOWN_SRC_RDY_N  => PORT1.DOWN.SRC_RDY_N,
      PORT1_DOWN_DST_RDY_N  => PORT1.DOWN.DST_RDY_N,
      PORT1_UP_DATA         => PORT1.UP.DATA,
      PORT1_UP_SOP_N        => PORT1.UP.SOP_N,
      PORT1_UP_EOP_N        => PORT1.UP.EOP_N,
      PORT1_UP_SRC_RDY_N    => PORT1.UP.SRC_RDY_N,
      PORT1_UP_DST_RDY_N     => PORT1.UP.DST_RDY_N,

      PORT2_DOWN_DATA       => PORT2.DOWN.DATA,
      PORT2_DOWN_SOP_N      => PORT2.DOWN.SOP_N,
      PORT2_DOWN_EOP_N      => PORT2.DOWN.EOP_N,
      PORT2_DOWN_SRC_RDY_N  => PORT2.DOWN.SRC_RDY_N,
      PORT2_DOWN_DST_RDY_N  => PORT2.DOWN.DST_RDY_N,
      PORT2_UP_DATA         => PORT2.UP.DATA,
      PORT2_UP_SOP_N        => PORT2.UP.SOP_N,
      PORT2_UP_EOP_N        => PORT2.UP.EOP_N,
      PORT2_UP_SRC_RDY_N    => PORT2.UP.SRC_RDY_N,
      PORT2_UP_DST_RDY_N     => PORT2.UP.DST_RDY_N
 );

end architecture IB_SWITCH_ARCH;
