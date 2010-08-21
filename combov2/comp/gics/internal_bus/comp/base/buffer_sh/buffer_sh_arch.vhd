--
-- buffer_sh_arch.vhd : Buffer composed of shift elements architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--      ARCHITECTURE DECLARATION  --  Buffer composed of shift elements      --
-- ----------------------------------------------------------------------------

architecture ib_buffer_sh_arch of IB_BUFFER_SH is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal empty : std_logic;
   signal full  : std_logic;
   signal we    : std_logic;
   signal re    : std_logic;
   signal din   : std_logic_vector(DATA_WIDTH-1+2 downto 0);
   signal dout  : std_logic_vector(DATA_WIDTH-1+2 downto 0);

begin

   -- DATA BUFFER -------------------------------------------------------------
   U_ib_buffer_sh_fifo: entity work.SH_FIFO
   generic map (
      FIFO_WIDTH     => DATA_WIDTH + 2,
      FIFO_DEPTH     => ITEMS,
      USE_INREG      => false, 
      USE_OUTREG     => false  
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      -- write interface
      DIN            => din,
      WE             => we,
      FULL           => full,
      -- read interface
      DOUT           => dout,
      RE             => re,
      EMPTY          => empty,
      -- status
      STATUS         => open
   );

   -- INPUT logic -------------------------------------------------------------
   din           <= IN_SOF_N&IN_EOF_N&IN_DATA;

   we            <= not IN_SRC_RDY_N and not full;

   IN_DST_RDY_N  <= full or RESET;

   -- OUTPUT logic ------------------------------------------------------------
   OUT_DATA      <= dout(DATA_WIDTH-1 downto 0);
   OUT_SOF_N     <= dout(DATA_WIDTH+1); 
   OUT_EOF_N     <= dout(DATA_WIDTH);

   OUT_SRC_RDY_N <= empty;

   re            <= not OUT_DST_RDY_N and not empty;
   
end ib_buffer_sh_arch;

                     

