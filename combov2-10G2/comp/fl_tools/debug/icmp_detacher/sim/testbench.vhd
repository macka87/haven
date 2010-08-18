-- testbench.vhd: frame link icmp_detacher testbench
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;
use work.math_pack.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;

library work;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
ENTITY testbench IS
END testbench;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
ARCHITECTURE testbench OF testbench IS

-- f = 100 MHz
constant clkper :time := 10 ns;

constant fl_bfm_id  : integer := 0;     -- ID of fl_bfm component
constant data_width : integer := 64;    -- data width

signal clk   : std_logic := '0';
signal reset : std_logic;

-- Input interface
signal rx_data      : std_logic_vector(data_width-1 downto 0);
signal rx_rem       : std_logic_vector(log2(data_width/8)-1 downto 0);
signal rx_src_rdy_n : std_logic;
signal rx_dst_rdy_n : std_logic;
signal rx_sop_n     : std_logic;
signal rx_eop_n     : std_logic;
signal rx_sof_n     : std_logic;
signal rx_eof_n     : std_logic;
  
-- Output interface
signal tx_data      : std_logic_vector(data_width-1 downto 0);
signal tx_rem       : std_logic_vector(log2(data_width/8)-1 downto 0);
signal tx_src_rdy_n : std_logic;
signal tx_dst_rdy_n : std_logic;
signal tx_sop_n     : std_logic;
signal tx_eop_n     : std_logic;
signal tx_sof_n     : std_logic;
signal tx_eof_n     : std_logic;

begin

uut : entity work.fl_icmp_detacher
   port map(
      CLK            => clk,
      RESET          => reset,

      -- write interface
      RX_DATA        => rx_data,
      RX_REM         => rx_rem,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
    
      -- read interface
      TX_DATA        => tx_data,
      TX_REM         => tx_rem,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n
   );

fl_bfm_0 : entity work.fl_bfm
   generic map(
      DATA_WIDTH      => data_width,
      FL_BFM_ID       => fl_bfm_id
   )
   port map(
      CLK          => clk,
      RESET        => reset,

      TX_DATA      => rx_data,
      TX_REM       => rx_rem,
      TX_SRC_RDY_N => rx_src_rdy_n,
      TX_DST_RDY_N => rx_dst_rdy_n,
      TX_SOP_N     => rx_sop_n,
      TX_EOP_N     => rx_eop_n,
      TX_SOF_N     => rx_sof_n,
      TX_EOF_N     => rx_eof_n         
   );

monitor : entity work.monitor
   generic map(
      RX_TX_DATA_WIDTH  => data_width,
      FILE_NAME         => "./data/icmp_det_out.txt",
      FRAME_PARTS       => 2,
      RDY_DRIVER        => RND
   )
   port map(
      FL_RESET          => reset,
      FL_CLK            => clk,
       
      RX_DATA           => tx_data,
      RX_REM            => tx_rem,
      RX_SOF_N          => tx_sof_n,
      RX_EOF_N          => tx_eof_n,
      RX_SOP_N          => tx_sop_n,
      RX_EOP_N          => tx_eop_n,
      RX_SRC_RDY_N      => tx_src_rdy_n,
      RX_DST_RDY_N      => tx_dst_rdy_n
   );

-- Clock generation - 100 MHz
local_clock : process
begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
end process;
      
-- Test bench circuit
fl_icmp_detacher_test : process
begin
    reset <= '1';
    wait for 50 ns;
   
    reset <= '0';
    
    SendWriteFile("./data/icmp_det_sim.txt", RND, flCmd_0, 0);
end process;

end;
