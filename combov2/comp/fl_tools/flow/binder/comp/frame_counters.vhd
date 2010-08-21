-- frame_counters.vhd: Set of Frame Counters
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_FRAME_COUNTERS is
   generic(
      COUNTER_WIDTH  : integer;
      COUNT          : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;
      
      -- input interface
      INC            : in std_logic_vector(COUNT-1 downto 0);
      DEC            : in std_logic_vector(COUNT-1 downto 0);
      
      -- output interface
      FRAME_RDY      : out std_logic_vector(COUNT-1 downto 0);
      NO_FRAME       : out std_logic
   );
end entity FLB_FRAME_COUNTERS;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of FLB_FRAME_COUNTERS is

   signal sig_frame_rdy    : std_logic_vector(COUNT-1 downto 0);
begin
   -- output signals
   FRAME_RDY   <= sig_frame_rdy;

   -- generate frame counters
   GEN_COUNTER : for i in 0 to COUNT-1 generate
       FLB_FRAME_COUNTER_I : entity work.FLB_FRAME_COUNTER
         generic map(
            COUNTER_WIDTH  => COUNTER_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            -- input interface
            INC            => INC(i),
            DEC            => DEC(i),
            -- output interface
            FRAME_RDY      => sig_frame_rdy(i)
         );
   end generate;
   
   -- NO_FRAME signal generic OR
   no_framep : process(sig_frame_rdy)
      variable or_int : std_logic;
   begin
      or_int := '0';
      
      for k in 0 to COUNT - 1 loop
         or_int := or_int or sig_frame_rdy(k);
      end loop;

      NO_FRAME <= not or_int;
   end process;

end architecture behavioral;

