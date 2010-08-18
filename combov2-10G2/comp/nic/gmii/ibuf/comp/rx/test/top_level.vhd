-- top_level.vhd : Combo top level entity
-- Copyright (C) 2005 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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
-- TODO list :
--
-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
--use work.addr_space.all;
--
-- pragma translate_off
--library unisim;
--use unisim.vcomponents.all;
-- pragma translate_on
entity fpga is
     port(
      RESET     : in  std_logic;

      -- RX gmii interface
      RXCLK   : in  std_logic;
      RXDV    : in  std_logic;
      RXER    : in  std_logic;
      RXD     : in  std_logic_vector(7 downto 0);

      -- ibuf_gmii_buf interface
      DO      : out std_logic_vector(7 downto 0);
      DO_DV   : out std_logic;
      STAT    : out std_logic_vector(1 downto 0);
      STAT_DV : out std_logic;
      SOP     : out std_logic
   );
end entity fpga;
-- --------------------------------------------------------------------
--                      Architecture declaration
-- --------------------------------------------------------------------
architecture behavioral of fpga is

-- ------------------------ Clk generation -----------------------------



-- ------------------------------------------------------------------
--                      Signal declaration
-- ------------------------------------------------------------------
      signal reg_RXD        : std_logic_vector(7 downto 0);
      signal reg_RXDV     : std_logic;
      signal reg_RXER      : std_logic;

      -- backend interface
      signal DO_i    : std_logic_vector(7 downto 0);
      signal reg_DO    : std_logic_vector(7 downto 0);
      signal DO_DV_i    : std_logic;
      signal reg_DO_DV    : std_logic;

      signal STAT_i    : std_logic_vector(1 downto 0);
      signal reg_STAT    : std_logic_vector(1 downto 0);
      signal STAT_DV_i    : std_logic;
      signal reg_STAT_DV    : std_logic;
      signal SOP_i : std_logic;
      signal reg_SOP : std_logic;

-- ------------------------------------------------------------------
--                       Architecture body
-- ------------------------------------------------------------------

begin
uut : entity work.ibuf_gmii_rx
port map(
   RESET     => reset,

   -- RX gmii interface
   RXCLK    => rxclk,
   RXDV     => reg_rxdv,
   RXER     => reg_rxer,
   RXD      => reg_rxd,

   -- buffer interface
   DO      => do_i,
   DO_DV   => do_dv_i,
   STAT    => stat_i,
   STAT_DV => stat_dv_i,
   SOP     => sop_i
);

-- ----------------------------------------------------------------------
reg_p: process(RESET,RXCLK)
begin
   if (RESET='1') then
      reg_RXD         <= (others=>'0');
      reg_RXDV        <= '0';
      reg_RXER        <= '0';
      reg_DO	<= (others=>'0');
      reg_DO_DV	<= '0';
      reg_STAT	<= (others=>'0');
      reg_STAT_DV	<= '0';
      reg_SOP  <= '0';
   elsif (rxclk'event and rxclk='1') then
      reg_RXD         <= RXD;
      reg_RXDV        <= RXDV;
      reg_RXER        <= RXER;
      reg_DO	<= DO_i;
      reg_DO_DV	<= DO_DV_i;
      reg_STAT	<= STAT_i;
      reg_STAT_DV <= STAT_DV_i;
      reg_SOP <= SOP_i;
   end if;
end process;

DO <= reg_DO;
DO_DV <= reg_DO_DV;
STAT <= reg_STAT;
STAT_DV <= reg_STAT_DV;
SOP <= reg_SOP;

end architecture behavioral;

