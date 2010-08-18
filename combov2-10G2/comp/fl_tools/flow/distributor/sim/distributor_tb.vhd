--
-- disp_tb.vhd: Component testbench.
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
	constant INTERFACES_COUNT : integer := 2;
	constant DEFAULT_INTERFACE : integer := 1;
	constant INUM_OFFSET : integer := DATA_WIDTH;

   constant clkper      : time      := 10 ns;
   constant INIT_TIME   : time      := 4*clkper + 10*clkper;
   constant RESET_TIME  : time      := 3*clkper;

   -- Packet parameters
   signal clk      : std_logic;
   signal reset    : std_logic;

   signal rx_data      : std_logic_vector(DATA_WIDTH - 1 downto 0); 
   signal rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0); 
   signal rx_src_rdy_n : std_logic;
   signal rx_dst_rdy_n : std_logic;
   signal rx_sop_n     : std_logic;
   signal rx_eop_n     : std_logic;
   signal rx_sof_n     : std_logic;
   signal rx_eof_n     : std_logic;

   signal tx_data     : std_logic_vector(INTERFACES_COUNT*DATA_WIDTH - 1 downto 0); 
   signal tx_rem      : std_logic_vector(INTERFACES_COUNT*log2(DATA_WIDTH/8) - 1 downto 0); 
   signal tx_src_rdy_n: std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_dst_rdy_n: std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_sop_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_eop_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_sof_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);
   signal tx_eof_n    : std_logic_vector(INTERFACES_COUNT-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   UUT: entity work.fl_distributor 
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         INTERFACES_COUNT  => INTERFACES_COUNT,
         DEFAULT_INTERFACE => DEFAULT_INTERFACE,
			INUM_OFFSET => INUM_OFFSET,
			PARTS => 1
      )
      port map (
         CLK          => CLK,
         RESET        => RESET,
   
         -- Write interface 
         RX_DATA      => rx_data,
         RX_REM       => rx_rem,
         RX_SRC_RDY_N => rx_src_rdy_n,
         RX_DST_RDY_N => rx_dst_rdy_n,
         RX_SOP_N     => rx_sop_n,
         RX_EOP_N     => rx_eop_n,
         RX_SOF_N     => rx_sof_n,
         RX_EOF_N     => rx_eof_n,
         
         -- Read interface
         TX_DATA     => tx_data,
         TX_REM      => tx_rem,
         TX_SRC_RDY_N=> tx_src_rdy_n,
         TX_DST_RDY_N=> tx_dst_rdy_n,
         TX_SOP_N    => tx_sop_n,
         TX_EOP_N    => tx_eop_n,
         TX_SOF_N    => tx_sof_n,
         TX_EOF_N    => tx_eof_n
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


-- Data input generator -------------------------------
digen: process
begin
   rx_data        <= (others =>'0');
   rx_rem         <= (others => '0');
   rx_sop_n       <= '1';
   rx_eop_n       <= '1';
   rx_sof_n       <= '1';
   rx_eof_n       <= '1';
   rx_src_rdy_n   <= '1';
	tx_dst_rdy_n	<= (others => '1');
	reset <= '1';
	
	for i in 10 downto 0 loop
		wait until clk'event and clk = '1';
	end loop;
   
	tx_dst_rdy_n	<= (others => '0');
	rx_src_rdy_n <= '0';
	rx_data <= (DATA_WIDTH-1 downto 0 => '1');
	rx_rem <= (others => '1');
	rx_sof_n <= '0';
	rx_eof_n <= '0';
	rx_eop_n <= '1';
	rx_eof_n <= '1';

	while(rx_dst_rdy_n = '1') loop
		wait until clk'event and clk = '1';
		reset <= '0';
	end loop;
	
	tx_dst_rdy_n	<= (others => '0');
   rx_src_rdy_n <= '0';
	rx_data <= (DATA_WIDTH-1 downto 2 => '1', 1 downto 0 => '0');
	rx_rem <= (others => '1');
	rx_sof_n <= '0';
	rx_eof_n <= '0';
	rx_eop_n <= '1';
	rx_eof_n <= '1';
   
	wait until clk'event and clk = '1';
   rx_src_rdy_n <= '1';
	tx_dst_rdy_n	<= (others => '0');
	wait until clk'event and clk = '1';
	tx_dst_rdy_n	<= (others => '0');
   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
