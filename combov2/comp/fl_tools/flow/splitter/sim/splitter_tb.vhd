--
-- splitter_tb.vhd: Testbench for FrameLink Splitter
-- Copyright (C) 2003 CESNET
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
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

   constant TEST_WIDTH  : integer   := 16;
   constant TEST_COUNT  : integer   := 2;
   constant FRAME_PARTS : integer   := 2;
   
   constant clkper      : time      := 10 ns;

   -- ------------------ Signals declaration ----------------------------------
   signal clk            : std_logic;
   signal reset          : std_logic;
   -- input interface
   signal rx_sof_n       : std_logic;
   signal rx_sop_n       : std_logic;
   signal rx_eop_n       : std_logic;
   signal rx_eof_n       : std_logic;
   signal rx_src_rdy_n   : std_logic;
   signal rx_dst_rdy_n   : std_logic;
   signal rx_data        : std_logic_vector(TEST_WIDTH-1 downto 0);
   signal rx_rem         : std_logic_vector(log2(TEST_WIDTH/8)-1 downto 0);
   -- output interface
   signal tx_sof_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_sop_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_eop_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_eof_n       : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_src_rdy_n   : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_dst_rdy_n   : std_logic_vector(TEST_COUNT-1 downto 0);
   signal tx_data        : std_logic_vector(TEST_COUNT*TEST_WIDTH-1 downto 0);
   signal tx_rem         : std_logic_vector(TEST_COUNT*log2(TEST_WIDTH/8)-1 
                                                                     downto 0);
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin


   uut : entity work.FL_SPLITTER
      generic map(
         DATA_WIDTH     => TEST_WIDTH,
         OUTPUT_COUNT   => TEST_COUNT,
	 FRAME_PARTS    => FRAME_PARTS
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         -- output interace
         TX_SOF_N       => tx_sof_n,
         TX_SOP_N       => tx_sop_n,
         TX_EOP_N       => tx_eop_n,
         TX_EOF_N       => tx_eof_n,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n,
         TX_DATA        => tx_data,
         TX_REM         => tx_rem
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
   
   -- send imaginary "packet" to splitter input
   procedure fls_send_packet(
      p_offset    : in integer;
      p_length    : in integer
   ) is
   begin
      rx_sof_n    <= '1';
      rx_sop_n    <= '1';
      rx_eop_n    <= '1';
      rx_eof_n    <= '1';
      rx_rem      <= (others => '0');

      rx_src_rdy_n<= '0';

      -- send 4 cycles of Control Data
      rx_sof_n    <= '0';
      rx_sop_n    <= '0';
      rx_data     <= conv_std_logic_vector(p_offset, TEST_WIDTH);
      wait for clkper;
      rx_sof_n    <= '1';
      rx_sop_n    <= '1';
      
      rx_data <= conv_std_logic_vector(p_offset+1, TEST_WIDTH);
      wait for clkper;
      rx_data <= conv_std_logic_vector(p_offset+2, TEST_WIDTH);
      wait for clkper;
      rx_data <= conv_std_logic_vector(p_offset+3, TEST_WIDTH);
      rx_eop_n    <= '0';
      rx_rem      <= conv_std_logic_vector(1, log2(TEST_WIDTH/8));
      wait for clkper;
      rx_rem      <= (others => '0');
      
      -- send remaining payload data
      rx_eop_n    <= '1';
      rx_sop_n    <= '0';
      rx_data     <= conv_std_logic_vector(p_offset+4, TEST_WIDTH);
      wait for clkper;
      rx_sop_n    <= '1';

      for i in p_offset+5 to p_offset+p_length-7 loop
         rx_data <= conv_std_logic_vector(i, TEST_WIDTH);

         wait for clkper;
      end loop;
      
      rx_data     <= conv_std_logic_vector(p_offset+p_length-6, TEST_WIDTH);
      rx_rem      <= (others => '0');
      rx_eop_n    <= '0';
      rx_eof_n    <= '0';
      wait for clkper;
      rx_eof_n    <= '1';
      rx_eop_n    <= '1';
      rx_src_rdy_n <= '1';

   end fls_send_packet;

begin
   reset <= '1';
   
   rx_sof_n     <= '1';
   rx_sop_n     <= '1';
   rx_eop_n     <= '1';
   rx_eof_n     <= '1';
   rx_data      <= (others => '0');
   rx_rem       <= (others => '0');
   rx_src_rdy_n <= '1';
   tx_dst_rdy_n <= "11";

   wait for 16*clkper;
   reset <= '0';

   wait for 5*clkper;

   tx_dst_rdy_n <= "00";
   
   fls_send_packet(1, 16);
   fls_send_packet(10, 32);
   fls_send_packet(3, 8);

   wait;
end process;

end architecture behavioral;
