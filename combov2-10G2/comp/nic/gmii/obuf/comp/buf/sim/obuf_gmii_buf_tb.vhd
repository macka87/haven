--
-- obuf_gmii_buf_tb.vhd: Testbench for obuf gmii buf part
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii_buf_tb is
end entity obuf_gmii_buf_tb;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of obuf_gmii_buf_tb is

   constant wr_clkper  : time    := 10 ns;
   constant tx_clkper  : time    :=  8 ns;
   constant DATA_PATHS : integer :=  1;
   
   signal wrclk        : std_logic;
   signal reset        : std_logic;
   signal dfifo_di     : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_wr     : std_logic;
   signal dfifo_full   : std_logic;

   signal sfifo_di     : std_logic_vector(0 downto 0);
   signal sfifo_wr     : std_logic;
   signal sfifo_full   : std_logic;

   signal tx_clk       : std_logic;
   signal tx_do        : std_logic_vector(7 downto 0);
   signal tx_dv        : std_logic;
   signal tx_er        : std_logic;
   signal tx_busy      : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping
-- ----------------------------------------------------

UUT : entity work.obuf_gmii_buf
generic map(
   ADDR_BASE  => 0,
   ADDR_WIDTH => 0,

   DATA_PATHS => DATA_PATHS,

   DFIFO_SIZE => 10*384,
   SFIFO_SIZE => 10,

   CTRL_CMD   => false

)
port map(
   RESET => reset,

   -- obuf_gmii_cmd interface
   WRCLK        => wrclk,

   DFIFO_DI     => dfifo_di,
   DFIFO_WR     => dfifo_wr,
   DFIFO_FULL   => dfifo_full,
   
   SFIFO_DI     => sfifo_di,
   SFIFO_WR     => sfifo_wr,
   SFIFO_FULL   => sfifo_full,
	  
   -- obuf_gmii_tx interface
   TX_CLK       => tx_clk,
   TX_DO        => tx_do,
   TX_DV        => tx_dv,
   TX_ER        => tx_er,
   TX_BUSY      => tx_busy,

   ADC_RD       => '0',
   ADC_WR       => '0',
   ADC_ADDR     => (others=>'0'),
   ADC_DI       => (others=>'0'),
   ADC_DO       => open,
   ADC_DRDY     => open
);


-- ----------------------------------------------------
-- wrclk clock generator
wrclk_clkgen : process
begin
   wrclk <= '1';
   wait for wr_clkper/2;
   wrclk <= '0';
   wait for wr_clkper/2;
end process;

-- tx_clk clock generator
tx_clk_clkgen : process
begin
   tx_clk <= '1';
   wait for tx_clkper/2;
   tx_clk <= '0';
   wait for tx_clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

in_p : process

begin
   dfifo_di     <= (others=>'0');
   dfifo_wr     <= '0';

   sfifo_di     <= (others=>'0');
   sfifo_wr     <= '0';

   reset        <= '1';

   wait for 100 ns;
   reset <= '0';
   
   for k in 1 to 3 loop

   for i in 0 to 5 loop
   
      wait until wrclk'event and wrclk='1';
      for j in 0 to DATA_PATHS-1 loop
         dfifo_di(DATA_PATHS*9-DATA_PATHS+j) <= '1';
	 dfifo_di((j+1)*8-1 downto j*8) <= conv_std_logic_vector(i, 4) & conv_std_logic_vector(j, 4);
      end loop;
      dfifo_wr <= '1';

   end loop;

   wait until wrclk'event and wrclk='1';
   dfifo_di <= (others=>'0');
   dfifo_wr <= '1';

   wait until wrclk'event and wrclk='1';

   sfifo_di <= "1";
   sfifo_wr <= '1';


   end loop;

   wait;
end process;

out_p : process
begin
   tx_busy <= '0';
   wait until tx_dv='1';
   tx_busy <= '1';
   wait until tx_dv='0';
   wait for tx_clkper*12;
   
   --tx_busy <= '0';

   --wait;
end process;

end architecture behavioral;
