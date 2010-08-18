--
-- sorting_unit_testbench.vhd: Component testbench.
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor xpusvi00@stud.fit.vutbr.cz
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DATA_WIDTH     : integer := 32;
   constant SORT_ITEMS     : integer := 4;
   constant DISTMEM_TYPE   : integer := 16;
   
   constant ADDR_WIDTH     : integer := log2(SORT_ITEMS);

   constant clkper      : time      := 10 ns;
   constant INIT_TIME   : time      := 2*SORT_ITEMS*clkper + 10*clkper;
   constant RESET_TIME  : time      := 3*clkper;

   signal clk      : std_logic;
   signal reset    : std_logic;

   signal rx_id         : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal rx_data       : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal rx_src_rdy_n  : std_logic;
   signal rx_dst_rdy_n  : std_logic;

   signal tx_id         : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal tx_data       : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal tx_src_rdy_n  : std_logic;
   signal tx_dst_rdy_n  : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   UUT: entity work.sorting_unit
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         SORT_ITEMS     => SORT_ITEMS,
         DISTMEM_TYPE   => DISTMEM_TYPE
      )
      port map(
         -- Common interface
         CLK            => clk,
         RESET          => reset,
   
         -- Write port
         RX_ID          => rx_id,
         RX_DATA        => rx_data,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
   
         -- Read port
         TX_ID          => tx_id,
         TX_DATA        => tx_data,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n
      );


-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin


   -- RESET ---------------------------------------------------------------
   reset <= '1';
   rx_id <= (others => '0');
   rx_data <= (others => '0');
   rx_src_rdy_n <= '1';

   tx_dst_rdy_n <= '1';

   wait for RESET_TIME;
   reset <= '0';

   wait for INIT_TIME;

   tx_dst_rdy_n <= '0';

--    wait for clkper/6;
   wait until (clk'event and clk = '1');

   -- Write first word - should come out in the TX part
   rx_id <= (others => '0');
   rx_data <= (others => '1');
   rx_src_rdy_n <= '0';
   wait for clkper;
   rx_src_rdy_n <= '1';


   wait for 10*clkper;


   -- Write FULL - ordered
   for i in 1 to SORT_ITEMS*2 - 1 loop
      rx_id          <= conv_std_logic_vector(i, rx_id'length);
      rx_data        <= conv_std_logic_vector(i, rx_data'length);
      rx_src_rdy_n   <= '0';
      wait for clkper;
   end loop;

   rx_src_rdy_n <= '1';


   wait for 10*clkper;


   -- Worst case - inverted order
   for i in SORT_ITEMS*2 - 1  downto 0 loop
      rx_id          <= conv_std_logic_vector(i, rx_id'length);
      rx_data        <= conv_std_logic_vector(i, rx_data'length);
      rx_src_rdy_n   <= '0';
      wait for clkper;
   end loop;

   rx_src_rdy_n <= '1';


   wait for 10*clkper;


   -- And even the more Worst case - ordered, but the first is the last
   for i in 1 to SORT_ITEMS - 1  loop
      rx_id          <= conv_std_logic_vector(i, rx_id'length);
      rx_data        <= conv_std_logic_vector(i, rx_data'length);
      rx_src_rdy_n   <= '0';
      wait for clkper;
   end loop;

   rx_id <= conv_std_logic_vector(0, rx_id'length);
   wait for clkper;
   
   -- And after that, write immediately the word with 0 ID
   for i in 0 to SORT_ITEMS - 1 loop
      rx_id          <= conv_std_logic_vector(i, rx_id'length);
      rx_data        <= conv_std_logic_vector(i, rx_data'length);
      rx_src_rdy_n   <= '0';
      wait for clkper;
   end loop;

   
   rx_src_rdy_n <= '1';


   wait for 10*clkper;


   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
