--
-- tb_local_compl_buf.vhd: For whole design testing
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

	  constant LOCAL_TAG_WIDTH		: integer := 5;		-- 'Local' Tag width
     constant LIMIT              : integer := 4;      -- Number of actually free items in buffer when TRANS_EN_N signal is asserted  
 
      -- clock & reset --------------------------------------------------------
      signal clk           : std_logic;  	-- FPGA clock
      signal reset         : std_logic;  	-- Reset active high

	   -- write interface ------------------------------------------------------
       signal rx_tc        : std_logic_vector( 2 downto 0); 		-- Traffic Class   
	   signal rx_attr       : std_logic_vector( 1 downto 0); 		-- Attributes
	   signal rx_tag        : std_logic_vector( 7 downto 0); 		-- Transaction Tag
	   signal rx_wr_0	      : std_logic;								   -- Write Request 0
	   signal rx_req_id	   : std_logic_vector(15 downto 0);			-- Requester ID (BUS, DEVICE, FUNCTION)
	   signal rx_wr_1	      : std_logic;								   -- Write Request 1

	   signal rx_allow	   : std_logic;								   -- Allow to write
	   signal rx_local_tag  : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0);	-- Local Tag
	   signal rx_full	      : std_logic;								   -- Local Buffer Full

	   -- read interface -------------------------------------------------------
      signal tx_tc         : std_logic_vector( 2 downto 0); 		-- Traffic Class     
      signal tx_attr       : std_logic_vector( 1 downto 0); 		-- Attributes     
      signal tx_tag        : std_logic_vector( 7 downto 0); 		-- Transaction Tag     
      signal tx_req_id     : std_logic_vector(15 downto 0); 		-- Requester ID (BUS, DEVICE, FUNCTION)

      signal tx_rd         : std_logic;  							      -- Read Request
      signal tx_rtag       : std_logic_vector(LOCAL_TAG_WIDTH-1 downto 0); 	-- Read Address

      signal status        : std_logic_vector(LOCAL_TAG_WIDTH downto 0); -- Number of pending Read Requests
      signal trans_en_n    : std_logic;                              -- Enable transaction

      constant clkper      : time         := 10 ns;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.LOCAL_COMPL_BUF
   generic map(
       LOCAL_TAG_WIDTH	=> LOCAL_TAG_WIDTH, -- 'Local' Tag width
       LIMIT            => LIMIT
   )
   port map(
      -- clock & reset --------------------------------------------------------
      CLK            => clk,  	-- FPGA clock
      RESET          => reset, 	-- Reset active high

	  -- Write interface ------------------------------------------------------
	   RX_TAG         => rx_tag,	   -- Transaction Tag
	   RX_WR_0		   => rx_wr_0,    -- Write Request 0
	   RX_REQ_ID		=> rx_req_id,  -- Requester ID (BUS, DEVICE, FUNCTION)
	   RX_WR_1		   => rx_wr_1,	   -- Write Request 1

	   RX_ALLOW		   => rx_allow,   -- Aloow to write
	   RX_LOCAL_TAG	=> rx_local_tag,-- Local Tag
	   RX_FULL		   => rx_full,	   -- Local Buffer Full

	   -- Read Interface -------------------------------------------------------
      TX_TAG         => tx_tag,	   -- Transaction Tag     
      TX_REQ_ID      => tx_req_id,  -- Requester ID (BUS, DEVICE, FUNCTION)

      TX_RD          => tx_rd,	   -- Read Request
      TX_RTAG        => tx_rtag,	   -- Read Address

      STATUS         => status,
      TRANS_EN_N     => trans_en_n
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

tb : process
begin

	reset 	<= '1';
	rx_wr_0	<= '0';
	rx_wr_1  <= '0';
	tx_rd 	<= '0';
	wait for clkper*10;

	
	reset 		<= '0';

   wait until (rx_allow = '1' and trans_en_n = '0');
	wait for clkper/20;

	-- init data
	rx_tag		<= "11001100";
	rx_req_id	<= X"DEAD";

	for i in 0 to 40 loop
      
      tx_rd       <= '0';
		rx_wr_0		<= '0';
		rx_wr_1		<= '0';   
      
      if(rx_allow = '1') then
		   tx_rd       <= '0';
		   rx_wr_0		<= '1';
		   rx_wr_1		<= '0';
      end if;

		wait for clkper;

	   -- test 1:
		if(i=10)then
		 	tx_rd <= '1';
		  	tx_rtag <= conv_std_logic_vector(3, tx_rtag'length);
		end if;

     	-- test 2:
		if(i=17)then
		 	tx_rd <= '1';
		  	tx_rtag <= conv_std_logic_vector(8, tx_rtag'length);
		end if; 
		  
      if(rx_allow = '1') then 
		   rx_wr_0		<= '0';
		   rx_wr_1		<= '1';
      end if;
      
		wait for clkper;
   
	   tx_rd <= '0';
         
	end loop;

	rx_wr_1 <= '0';
   reset <= '1';

   wait for clkper;

   reset <= '0';

	wait;

end process;


-- ----------------------------------------------------------------------------
end architecture behavioral;
