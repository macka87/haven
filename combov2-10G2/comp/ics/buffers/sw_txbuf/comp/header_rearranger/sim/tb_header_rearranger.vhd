-- relay_tb.vhd: Testbench for FrameLink header rearranger
-- Copyright (C) 2008 CESNET
-- Author(s): Ondrej Lengal <xlenga00@stud.fit.vutbr.cz>
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

   constant DATA_WIDTH  : integer   := 64;
   
   constant clkper      : time      := 10 ns;

   -- ------------------ Signals declaration ----------------------------------
   signal clk           : std_logic;
   signal reset         : std_logic;

   -- input interface
   signal rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0)
                        := (others => '0');
   signal rx_drem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
                        := (others => '0');
   signal rx_sof_n      : std_logic := '1';
   signal rx_sop_n      : std_logic := '1';
   signal rx_eop_n      : std_logic := '1';
   signal rx_eof_n      : std_logic := '1';
   signal rx_src_rdy_n  : std_logic := '1';
   signal rx_dst_rdy_n  : std_logic;

   signal rx_frm_has_header : std_logic;

   -- output interface
   signal tx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_drem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal tx_sof_n      : std_logic;
   signal tx_sop_n      : std_logic;
   signal tx_eop_n      : std_logic;
   signal tx_eof_n      : std_logic;
   signal tx_src_rdy_n  : std_logic;
   signal tx_dst_rdy_n  : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.header_rearranger
      generic map (
         DATA_WIDTH     => DATA_WIDTH
      )
      port map (
         CLK            => clk,
         RESET          => reset,

         -- input interface
         RX_DATA        => rx_data,
         RX_REM         => rx_drem,
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,

         FRAME_HAS_HEADER => rx_frm_has_header,

         -- output interace
         TX_DATA        => tx_data,
         TX_REM         => tx_drem,
         TX_SOF_N       => tx_sof_n,
         TX_SOP_N       => tx_sop_n,
         TX_EOP_N       => tx_eop_n,
         TX_EOF_N       => tx_eof_n,
         TX_SRC_RDY_N   => tx_src_rdy_n,
         TX_DST_RDY_N   => tx_dst_rdy_n
      );


-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- Input data generator (counter)
rx_datagen : process
begin
   rx_data <= rx_data + 1 after 0.1*clkper;
   wait for clkper;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
begin
   reset <= '1';

   rx_frm_has_header <= '0';
   rx_src_rdy_n <= '1';
   tx_dst_rdy_n <= '1';

   wait for 16*clkper;
   reset <= '0';

   wait for 2*clkper;

      -- Added to check if works rearanging  
   rx_frm_has_header <= '1';
   
   tx_dst_rdy_n <= '0';
   rx_src_rdy_n <= '0';
  

   rx_sof_n <= '0';
   rx_sop_n <= '0';
   wait for clkper;
   rx_sof_n <= '1';
   rx_sop_n <= '1';

   wait for 21*clkper;
   rx_eop_n <= '0';
   wait for clkper;
   rx_eop_n <= '1';
   rx_sop_n <= '0';
   wait for clkper;
   rx_sop_n <= '1';


   wait for 21*clkper;
   rx_eof_n <= '0';
   rx_eop_n <= '0';
   wait for clkper;
   rx_eof_n <= '1';
   rx_eop_n <= '1';
   rx_src_rdy_n <= '1';

   wait for 4*clkper;

   rx_frm_has_header <= '1';
   
   tx_dst_rdy_n <= '0';
   rx_src_rdy_n <= '0';
  
   wait for 2*clkper;

   rx_sof_n <= '0';
   rx_sop_n <= '0';
   wait for clkper;
   rx_sof_n <= '1';
   rx_sop_n <= '1';

   wait for 21*clkper;
   rx_eop_n <= '0';
   wait for clkper;
   rx_eop_n <= '1';
   rx_sop_n <= '0';
   wait for clkper;
   rx_sop_n <= '1';


   wait for 21*clkper;
   rx_eof_n <= '0';
   rx_eop_n <= '0';
   wait for clkper;
   rx_eof_n <= '1';
   rx_eop_n <= '1';
   rx_src_rdy_n <= '1';


   wait;

end process;

end architecture behavioral;

