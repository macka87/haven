--
-- tb_global_compl_buf.vhd: For whole design testing
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

	   constant LOCAL_TAG_WIDTH      : integer := 5;		-- 'Local' Tag width
      constant GLOBAL_TAG_WIDTH	   : integer := 5;		-- 'Global' Tag width
      constant LIMIT                : integer := 4;      -- Number of actually free items in buffer when TRANS_EN_N signal is asserted 
 
      -- clock & reset --------------------------------------------------------
      signal clk           : std_logic;  	-- FPGA clock
      signal reset         : std_logic;  	-- Reset active high

	   -- read interface -------------------------------------------------------
      signal rx_local_addr : std_logic_vector(31 downto 0); 				      -- Local Address     
      signal rx_local_tag  : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0); 	-- Local Tag     

      signal rx_rd     	   : std_logic;  								   	         -- Read Request
      signal rx_global_tag : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0);   -- Read Address

	   signal rx_last_cpl   : std_logic;										         -- Last Completion
	   signal rx_len_cpl	   : std_logic_vector(11 downto 0);					      -- Completion Length

	   -- write interface ------------------------------------------------------
      signal tx_local_addr : std_logic_vector(31 downto 0); 				      -- Local Address
	   signal tx_local_tag  : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);	   -- Local Tag
	   signal tx_wr		   : std_logic;										         -- Write Request
	  
      signal tx_allow      : std_logic;                                       -- Allow to write
      signal tx_full       : std_logic;                                       -- Global Buffer full 
	   signal tx_rtag 	   : std_logic_vector(GLOBAL_TAG_WIDTH-1 downto 0); 	-- Global Tag
      signal status        : std_logic_vector(GLOBAL_TAG_WIDTH downto 0);     -- Number of pending Read Requests
      signal trans_en_n    : std_logic;                                       -- Enable transaction

      constant clkper      : time         := 10 ns;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------

begin

uut : entity work.GLOBAL_COMPL_BUF
   generic map (
         LOCAL_TAG_WIDTH 		=> LOCAL_TAG_WIDTH,	   -- 'Local' Tag width
         GLOBAL_TAG_WIDTH 		=> GLOBAL_TAG_WIDTH,   -- 'Global' Tag width
         LIMIT                => LIMIT
      )  
   port map(
      -- clock & reset --------------------------------------------------------
      CLK           => clk, 	   -- FPGA clock
      RESET         => reset, 	-- Reset active high

	  -- Read Interface -------------------------------------------------------
      RX_LOCAL_ADDR  => rx_local_addr,	-- Local Address     
      RX_LOCAL_TAG   => rx_local_tag,	-- Local Tag     

      RX_RD       	=> rx_rd,			-- Read Request
      RX_GLOBAL_TAG  => rx_global_tag,	-- Read Address

	   RX_LAST_CPL	   => rx_last_cpl,   -- Last Completion
	   RX_LEN_CPL	   => rx_len_cpl,		-- Completion Length

	   -- Write interface ------------------------------------------------------
      TX_LOCAL_ADDR  => tx_local_addr,	-- Local Address
	   TX_LOCAL_TAG   => tx_local_tag,	-- Local Tag
	   TX_WR			   => tx_wr,			-- Write Request
	  
      TX_ALLOW       => tx_allow,      -- Allow to write
      TX_FULL        => tx_full,       -- Buffer full
	   TX_RTAG 		   => tx_rtag,			-- Global Tag

      STATUS         => status,
      TRANS_EN_N     => trans_en_n
   );
   -- -------------------------------------------------------------------------

-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

tb : process
begin

	reset 	      <= '1';
   tx_wr          <= '0';
   rx_rd          <= '0';
	wait for clkper*2;

	reset 	      <= '0';

   wait until (TRANS_EN_N = '0' and TX_ALLOW = '1');
   wait for clkper/20;

   -- init data
   tx_local_addr  <= X"DEADDEAD";
   tx_local_tag   <= "10001";
   
   rx_last_cpl    <= '0';
   rx_len_cpl     <= "000000000001";
   rx_global_tag  <= conv_std_logic_vector(0, rx_global_tag'length);

   wait for clkper;

   tx_wr          <= '1';
   wait for clkper;

   tx_wr          <= '0';
   wait for clkper;

   rx_rd          <= '1';
   wait for clkper*4;

   rx_last_cpl    <= '1';
   rx_rd          <= '1';
   wait for clkper;

   rx_rd          <= '0';
   wait for clkper;

   
   tx_wr          <= '1';
   wait for clkper*40;

   tx_wr          <= '0';
  
   reset <= '1';
   wait for clkper;

   reset <= '0';


	wait;

end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
