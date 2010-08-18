-- testbench.vhd: IB_ASFIFO testbench
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--	      Jan Stourac <xstour03@stud.fit.vutbr.cz>
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
--

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS


-- simulation constants
constant CLKPER_RX   : time      := 8 ns;
constant CLKPER_TX   : time      := 5 ns;

-- signals from/to tested unit
signal RX_CLK        : std_logic;
signal RX_RESET      : std_logic;
signal TX_CLK        : std_logic;
signal TX_RESET      : std_logic;

signal RX_DATA       : std_logic_vector(63 downto 0);
signal RX_SRC_RDY_N  : std_logic;
signal RX_DST_RDY_N  : std_logic;
signal RX_SOP_N      : std_logic;
signal RX_EOP_N      : std_logic;
      
signal TX_DATA       : std_logic_vector(63 downto 0);
signal TX_SRC_RDY_N  : std_logic;
signal TX_DST_RDY_N  : std_logic;
signal TX_SOP_N      : std_logic;
signal TX_EOP_N      : std_logic;

begin

-- Unit under test
uut: entity work.IB_ASFIFO_64B
port map(
   TX_CLK      => TX_CLK,
   TX_RESET    => TX_RESET,
   RX_CLK      => RX_CLK,
   RX_RESET    => RX_RESET,

   TX_DATA       => TX_DATA,
   TX_SRC_RDY_N  => TX_SRC_RDY_N,
   TX_DST_RDY_N  => TX_DST_RDY_N,
   TX_SOP_N      => TX_SOP_N,
   TX_EOP_N      => TX_EOP_N,

   RX_DATA       => RX_DATA,
   RX_SRC_RDY_N  => RX_SRC_RDY_N,
   RX_DST_RDY_N  => RX_DST_RDY_N,
   RX_SOP_N      => RX_SOP_N,
   RX_EOP_N      => RX_EOP_N
);

-- Clock generation
tx_clock: process
begin
   TX_CLK <= '1';
   wait for clkper_tx/2;
   TX_CLK <= '0';
   wait for clkper_tx/2;
end process;

rx_clock: process
begin
   RX_CLK <= '1';
   wait for clkper_rx/2;
   RX_CLK <= '0';
   wait for clkper_rx/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   RX_RESET       <= '1';
   TX_RESET       <= '1';
   RX_DATA     <= (others => '0');
   RX_SRC_RDY_N  <= '1';
   RX_SOP_N      <= '1';
   RX_EOP_N      <= '1';
   TX_DST_RDY_N  <= '1';

   wait for 4*clkper_rx;
   RX_RESET <= '0';
   TX_RESET <= '0';
   wait for 4*clkper_rx;
   
   -- Send frame
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(10, RX_DATA'length);
   RX_SOP_N   <= '0';
   TX_DST_RDY_N <= '0';
   wait for clkper_rx;  -- SOF

   RX_DATA  <= conv_std_logic_vector(11, RX_DATA'length);
   RX_SOP_N   <= '1';
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(12, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(13, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(14, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(15, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(16, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper_rx;  -- EOF

   RX_SRC_RDY_N <= '1';
   wait for clkper_rx;


wait;
end process;

end;
