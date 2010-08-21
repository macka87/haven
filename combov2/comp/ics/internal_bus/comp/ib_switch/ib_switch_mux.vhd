--
-- ib_switch_mux.vhd: ib_switch output multiplexor
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SWITCH_MUX is
   port(
   -- Data IN
   PORTO_DATA_IN  : in std_logic_vector(63 downto 0);
   PORT1_DATA_IN  : in std_logic_vector(63 downto 0);
   PORT2_DATA_IN  : in std_logic_vector(63 downto 0);
   
   -- Port 0 Data Out
   PORT0_DATA_OUT : out std_logic_vector(63 downto 0);
   PORT0_MUX_SEL  : in  std_logic_vector(1 downto 0);
   
   -- Port 1 Data Out
   PORT1_DATA_OUT : out std_logic_vector(63 downto 0);
   PORT1_MUX_SEL  : in  std_logic_vector(1 downto 0);
   
   -- Port 2 Data Out
   PORT2_DATA_OUT : out std_logic_vector(63 downto 0);
   PORT2_MUX_SEL  : in  std_logic_vector(1 downto 0)
   );
end entity IB_SWITCH_MUX;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_MUX_ARCH of IB_SWITCH_MUX is


begin

-- multiplexor port0 ----------------------------------------------------------
port0_muxp: process(PORT0_MUX_SEL, PORTO_DATA_IN, PORT1_DATA_IN, PORT2_DATA_IN)
begin
   case PORT0_MUX_SEL is
      when "01" => PORT0_DATA_OUT <= PORT1_DATA_IN;
      when "10" => PORT0_DATA_OUT <= PORT2_DATA_IN;
      when others => PORT0_DATA_OUT <= (others => '0');
   end case;
end process;

-- multiplexor port1 ----------------------------------------------------------
port1_muxp: process(PORT1_MUX_SEL, PORTO_DATA_IN, PORT1_DATA_IN, PORT2_DATA_IN)
begin
   case PORT1_MUX_SEL is
      when "00" => PORT1_DATA_OUT <= PORTO_DATA_IN;
      when "10" => PORT1_DATA_OUT <= PORT2_DATA_IN;
      when others => PORT1_DATA_OUT <= (others => '0');
   end case;
end process;

-- multiplexor port2 ----------------------------------------------------------
port2_muxp: process(PORT2_MUX_SEL, PORTO_DATA_IN, PORT1_DATA_IN, PORT2_DATA_IN)
begin
   case PORT2_MUX_SEL is
      when "00" => PORT2_DATA_OUT <= PORTO_DATA_IN;
      when "01" => PORT2_DATA_OUT <= PORT1_DATA_IN;
      when others => PORT2_DATA_OUT <= (others => '0');
   end case;
end process;


end architecture IB_SWITCH_MUX_ARCH;

