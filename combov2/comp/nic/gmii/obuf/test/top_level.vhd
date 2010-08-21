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
     port (
      RESET      : in  std_logic;

      -- command input interface
      WRCLK      : in  std_logic;
      WR         : in  std_logic;
      DI         : in  std_logic_vector((2*8-1) downto 0);
      DI_CMD     : in  std_logic_vector((2-1)   downto 0);
      FULL       : out std_logic;

      -- transmit gmii interface
      REFCLK     : in  std_logic;
      TXCLK      : out std_logic;
      TXD	 : out std_logic_vector(7 downto 0);
      TXEN	 : out std_logic;
      TXER	 : out std_logic;

      -- address decoder interface
      ADC_RD     : in  std_logic;
      ADC_WR     : in  std_logic;
      ADC_ADDR   : in  std_logic_vector(9-1 downto 0);
      ADC_DI     : in  std_logic_vector(31 downto 0);
      ADC_DO     : out std_logic_vector(31 downto 0);
      ADC_DRDY   : out std_logic
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
   
      signal txd_i        : std_logic_vector(7 downto 0);
      signal txen_i     : std_logic;
      signal txer_i      : std_logic;

      -- backend interface
      signal reg_TXD       : std_logic_vector(7 downto 0);
      signal reg_txen     : std_logic;
      signal reg_txer      : std_logic;
      signal reg_wr         : std_logic;
      signal reg_di        : std_logic_vector(15 downto 0);
      signal reg_di_cmd         : std_logic_vector(1  downto 0);
      signal full_i       : std_logic;
      signal reg_full       : std_logic;

-- ------------------------------------------------------------------
--                       Architecture body
-- ------------------------------------------------------------------

begin
uut : entity work.obuf_gmii
generic map (
   ADDR_BASE  => 0,
   ADDR_WIDTH => 9,
   DATA_PATHS => 2,
   DFIFO_SIZE => 8191,
   SFIFO_SIZE => 127
)
port map(
   RESET     => reset,

   -- RX gmii interface
   REFCLK   => REFCLK,
   TXCLK    => TXCLK,
   TXEN     => txen_i,
   TXER     => txer_i,
   TXD      => txd_i,

   WRCLK    => WRCLK,
   WR       => reg_wr,
   DI       => reg_di,
   DI_CMD   => reg_di_cmd,
   FULL     => full_i,

--   ADC_CLK  => ADC_CLK,
   ADC_RD   => ADC_RD,
   ADC_WR   => ADC_WR,
   ADC_ADDR => ADC_ADDR,
   ADC_DI   => ADC_DI,
   ADC_DO   => ADC_DO,
   ADC_DRDY => ADC_DRDY  
);

-- ----------------------------------------------------------------------
reg_tx_p: process(RESET,REFCLK)
begin
   if (RESET='1') then
      reg_TXD         <= (others=>'0');
      reg_TXEN        <= '0';
      reg_TXER        <= '0';
   elsif (REFCLK'event and REFCLK='1') then
      reg_TXD         <= TXD_i;
      reg_TXEN        <= TXEN_i;
      reg_TXER        <= TXER_i;
   end if;
end process;

reg_rd_p: process(RESET,WRCLK)
begin
   if (RESET='1') then
      reg_WR           <= '0';
      reg_DI           <= (others=>'0');
      reg_DI_CMD       <= (others=>'0');
      reg_FULL         <= '0';
   elsif (WRclk'event and WRclk='1') then
      reg_WR           <= WR;
      reg_DI           <= DI;
      reg_DI_CMD       <= DI_CMD;
      reg_FULL         <= full_i;
   end if;
end process;

FULL <= reg_full;
TXD  <= reg_TXD;
TXEN <= reg_TXEN;
TXER <= reg_TXEN;

end architecture behavioral;

