-- ib_rx8.vhd : Internal bus RX 8-bit SDR interface
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
library unisim;
use unisim.vcomponents.all;
use work.math_pack.all;


entity ib_rx8 is
   generic (
      DATA_WIDTH   : natural := 64); -- 8, 15, 32 or 64
   port (
      CLK          : in  std_logic; -- Data will be sychchronized with this clock
      RXCLK        : out std_logic;
      RESET        : in  std_logic;
      -- RX interface
      RX_DATA      : out std_logic_vector(DATA_WIDTH-1  downto 0);
      RX_SOP_N     : out std_logic;
      RX_EOP_N     : out std_logic;
      RX_SRC_RDY_N : out std_logic;
      RX_DST_RDY_N : in  std_logic;
      -- TX interface
      RX_PAD       : in  std_logic_vector(7 downto 0)
   );
end entity ib_rx8;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of ib_rx8 is

signal rxclk_i      : std_logic;
signal rx_data8     : std_logic_vector(7 downto 0);
signal rx_sof8      : std_logic;
signal rx_eof8      : std_logic;
signal rx_src_rdy8  : std_logic;
signal rx_dst_rdy8  : std_logic;      
signal rx_data8_i   : std_logic_vector(7 downto 0);
signal rx_sof8_i    : std_logic;
signal rx_eof8_i    : std_logic;
signal rx_src_rdy8_i: std_logic;
signal rx_pad_i     : std_logic_vector(7 downto 0);
signal rx_data8_clk   : std_logic_vector(7 downto 0);
signal rx_sof8_clk    : std_logic;
signal rx_eof8_clk    : std_logic;
signal rx_src_rdy8_clk: std_logic;

signal regiob_rx_data : std_logic_vector(7 downto 0) := X"FF";
signal regiob_rx_sof  : std_logic;
signal regiob_rx_eof  : std_logic;
signal regiob_rx_src_rdy  : std_logic;
signal sof_sync       : std_logic;
signal even           : std_logic := '0';

attribute register_balancing: string;
attribute register_balancing of rx_src_rdy8_i: signal is "no";
attribute register_balancing of rx_sof8_i: signal is "no";
attribute register_balancing of rx_eof8_i: signal is "no";
attribute register_balancing of rx_data8_i: signal is "no";

begin

   rx_dst_rdy8  <= '0';

   TRANSFORM: entity work.FL_TRANSFORMER_UP_8
   generic map (
      TX_DATA_WIDTH  => DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      -- RX interface
      RX_DATA        => rx_data8,
      RX_SOF_N       => rx_sof8,    
      RX_EOF_N       => rx_eof8,    
      RX_SOP_N       => rx_sof8,    
      RX_EOP_N       => rx_eof8,    
      RX_SRC_RDY_N   => rx_src_rdy8,
      RX_DST_RDY_N   => rx_dst_rdy8,
      -- TX interface
      TX_DATA        => RX_DATA,
      TX_REM         => open,
      TX_SOF_N       => open,
      TX_EOF_N       => open,
      TX_SOP_N       => RX_SOP_N,    
      TX_EOP_N       => RX_EOP_N,    
      TX_SRC_RDY_N   => RX_SRC_RDY_N,
      TX_DST_RDY_N   => RX_DST_RDY_N 
   );

-- DDR IOB registers
RX_REGS_RISE: process(RESET, rxclk_i)
begin
   if RESET = '1' then
      regiob_rx_sof              <= '1';
      regiob_rx_eof              <= '1';
      regiob_rx_src_rdy          <= '1';
   elsif rxclk_i'event and rxclk_i = '1' then -- Rising edge
      regiob_rx_data(3 downto 0) <= RX_PAD_I(3 downto 0);
      regiob_rx_sof              <= RX_PAD_I(4);
      regiob_rx_eof              <= RX_PAD_I(5);
      regiob_rx_src_rdy          <= RX_PAD_I(6);
   end if;
end process;

sof_sync <= '1' when (regiob_rx_sof = '0') and (regiob_rx_src_rdy = '0') else '0';

RX_REGS_SYNC: process(RESET, rxclk_i)
begin
   if RESET = '1' then
      rx_sof8_i              <= '1';
      rx_eof8_i              <= '1';
      rx_src_rdy8_i          <= '1';
   elsif rxclk_i'event and rxclk_i = '0' then -- Falling clock edge 
      -- Odd/even flag
      if (sof_sync = '1') then
         even <= '0';
      else
         even <= not even;
      end if;
      -- Data registers
      if (even = '1') or (sof_sync = '1') then
         rx_data8_i(3 downto 0) <= regiob_rx_data(3 downto 0);
         rx_sof8_i              <= regiob_rx_sof;
         rx_eof8_i              <= '1';
         rx_src_rdy8_i          <= '1';
      elsif (even = '0') then
         rx_data8_i(7 downto 4) <= regiob_rx_data(3 downto 0);
         rx_eof8_i              <= regiob_rx_eof;
         rx_src_rdy8_i          <= regiob_rx_src_rdy;
      end if;
   end if;
end process;


-- RX_REGS_FALL: process(rxclk_i)
-- begin
--    if rxclk_i'event and rxclk_i = '0' then -- Falling edge
--       regiob_rx_data(7 downto 4) <= RX_PAD_I(3 downto 0);
--    end if;
-- end process;

-- RX_FALL_RECLOCK: process(rxclk_i)
-- begin
--    if rxclk_i'event and rxclk_i = '0' then -- Falling edge
--       rx_data8_rec(7 downto 4) <= regiob_rx_data(7 downto 4);
--    end if;
-- end process;

-- RX_RISE_RECLOCK: process(rxclk_i)
-- begin
--    if rxclk_i'event and rxclk_i = '1' then -- Falling edge
--       rx_data8_i(7 downto 4) <= rx_data8_rec(7 downto 4);
--    end if;
-- end process;

-- RX_REG: process(rxclk_i)
-- begin
--    if rxclk_i'event and rxclk_i = '1' then -- Falling edge
--       rx_data8_i(3 downto 0)    <= regiob_rx_data(3 downto 0);
--       rx_sof8_i     <= regiob_rx_sof;
--       rx_eof8_i     <= regiob_rx_eof;
--       rx_src_rdy8_i <= regiob_rx_src_rdy;
--    end if;
-- end process;

-- Reclock data from the rxclk domain to the clk domain
RX_RECLOCK: process(RESET, CLK)
begin
   if RESET = '1' then
      rx_sof8     <= '1';
      rx_eof8     <= '1';
      rx_src_rdy8 <= '1';
   elsif CLK'event and CLK = '1' then 
      rx_data8    <= rx_data8_i;
      rx_sof8     <= rx_sof8_i;
      rx_eof8     <= rx_eof8_i;
      rx_src_rdy8 <= rx_src_rdy8_i;
   end if;
end process;

RXCLK    <= rxclk_i;
--rxclk_i  <= RX_PAD(7);
rx_pad_i <= RX_PAD after 1 ns; -- Delay the data (for simulation only)

IDELAY_RXCLK : IDELAY
generic map (
   IOBDELAY_TYPE  => "DEFAULT", -- "DEFAULT", "FIXED" or "VARIABLE"
   IOBDELAY_VALUE => 0)         -- Any value from 0 to 63
port map (
   O   => rxclk_i,   -- 1-bit output
   C   => '0',       -- 1-bit clock input
   CE  => '1',       -- 1-bit clock enable input
   I   => RX_PAD(7), -- 1-bit data input
   INC => '0',       -- 1-bit increment input
   RST => '0'        -- 1-bit reset input
);
    
end architecture behavioral;
