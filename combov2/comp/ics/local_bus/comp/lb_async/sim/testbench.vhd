-- testbench.vhd: LB_ASFIFO testbench
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

signal RX_DWR        : std_logic_vector(15 downto 0);           -- Input Data
signal RX_BE         : std_logic_vector(1 downto 0);            -- Byte Enable
signal RX_ADS_N      : std_logic;                               -- Address Strobe
signal RX_RD_N       : std_logic;                               -- Read Request
signal RX_WR_N       : std_logic;                               -- Write Request
signal RX_DRD        : std_logic_vector(15 downto 0);           -- Output Data
signal RX_RDY_N      : std_logic;                               -- Ready
signal RX_ERR_N      : std_logic;                               -- Error
signal RX_ABORT_N    : std_logic;                               -- Abort Transaction

signal TX_DWR        : std_logic_vector(15 downto 0);           -- Input Data
signal TX_BE         : std_logic_vector(1 downto 0);            -- Byte Enable
signal TX_ADS_N      : std_logic;                               -- Address Strobe
signal TX_RD_N       : std_logic;                               -- Read Request
signal TX_WR_N       : std_logic;                               -- Write Request
signal TX_DRD        : std_logic_vector(15 downto 0);           -- Output Data
signal TX_RDY_N      : std_logic;                               -- Ready
signal TX_ERR_N      : std_logic;                               -- Error
signal TX_ABORT_N    : std_logic;                               -- Abort Transaction

begin

-- Unit under test
uut: entity work.LB_ASYNC
port map(
   TX_CLK      => TX_CLK,
   TX_RESET    => TX_RESET,
   RX_CLK      => RX_CLK,
   RX_RESET    => RX_RESET,

   TX_DWR      => TX_DWR,
   TX_BE       => TX_BE,
   TX_ADS_N    => TX_ADS_N,
   TX_RD_N     => TX_RD_N,
   TX_WR_N     => TX_WR_N,
   TX_DRD      => TX_DRD,
   TX_RDY_N    => TX_RDY_N,
   TX_ERR_N    => TX_ERR_N,
   TX_ABORT_N  => TX_ABORT_N,

   RX_DWR      => RX_DWR,
   RX_BE       => RX_BE,
   RX_ADS_N    => RX_ADS_N,
   RX_RD_N     => RX_RD_N,
   RX_WR_N     => RX_WR_N,
   RX_DRD      => RX_DRD,
   RX_RDY_N    => RX_RDY_N,
   RX_ERR_N    => RX_ERR_N,
   RX_ABORT_N  => RX_ABORT_N
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


-- RX process
write_test: process
begin
   wait for 2 ns;
   RX_RESET  <= '1';
   RX_DWR    <= (others => '0');
   RX_BE     <= "00";
   RX_ADS_N  <= '1';
   RX_RD_N   <= '1';
   RX_WR_N   <= '1';
   RX_ABORT_N<= '1';

   wait for 4*clkper_rx;
   RX_RESET <= '0';
   wait for 7*clkper_rx;
   
   -- send data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(10, RX_DWR'length);
   RX_BE <= "11";
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(11, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N  <= '1';
   RX_WR_N   <= '0';
   RX_DWR  <= conv_std_logic_vector(12, RX_DWR'length);
   wait for clkper_rx;

   RX_WR_N   <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
   wait for 3*clkper_rx;

   -- receive data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(06, RX_DWR'length);
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(13, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N    <= '1';
   RX_RD_N     <= '0';
   wait for 2*clkper_rx;
   RX_RD_N     <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
   wait for 5*clkper_rx;

   -- send data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(10, RX_DWR'length);
   RX_BE <= "11";
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(11, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N  <= '1';
   RX_WR_N   <= '0';
   RX_DWR  <= conv_std_logic_vector(12, RX_DWR'length);
   wait for clkper_rx;

   RX_WR_N   <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
   wait for 3*clkper_rx;

   -- receive data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(06, RX_DWR'length);
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(13, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N    <= '1';
   RX_RD_N     <= '0';
   wait for 2*clkper_rx;
   RX_RD_N     <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
   wait for 5*clkper_rx;

-- send data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(10, RX_DWR'length);
   RX_BE <= "11";
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(11, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N  <= '1';
   RX_WR_N   <= '0';
   RX_DWR  <= conv_std_logic_vector(12, RX_DWR'length);
   wait for clkper_rx;
   RX_DWR  <= conv_std_logic_vector(13, RX_DWR'length);
   wait for clkper_rx;
   RX_DWR  <= conv_std_logic_vector(14, RX_DWR'length);
   wait for clkper_rx;
   RX_DWR  <= conv_std_logic_vector(15, RX_DWR'length);
   wait for clkper_rx;
   RX_WR_N   <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
   wait for 3*clkper_rx;

-- receive data
   RX_ADS_N  <= '0';
   RX_DWR  <= conv_std_logic_vector(06, RX_DWR'length);
   wait for clkper_rx;

   RX_DWR  <= conv_std_logic_vector(13, RX_DWR'length);
   wait for clkper_rx;

   RX_ADS_N    <= '1';
   RX_RD_N     <= '0';
   wait for 5*clkper_rx;
   RX_RD_N     <= '1';

   wait until RX_RDY_N <= '0';
   wait until RX_RDY_N <= '1';
wait;
end process;


-- TX process
read_test : process
begin
   wait for 2 ns;
   TX_RESET  <= '1';
   TX_DRD    <= (others => '0');
   TX_RDY_N  <= '1';
   TX_ERR_N  <= '1';

   wait for 4*clkper_tx;
   TX_RESET <= '0';
   wait for 7*clkper_tx;

   -- receive
   wait until TX_WR_N = '0';
   TX_RDY_N <= '0';
   wait for clkper_tx;
   TX_RDY_N <= '1';

   -- send data
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(15, TX_DRD'length);
   wait for clkper_tx;
   TX_DRD  <= conv_std_logic_vector(10, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';

   -- receive
   wait until TX_WR_N = '0';
   TX_RDY_N <= '0';
   wait for clkper_tx;
   TX_RDY_N <= '1';

   -- send data
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(15, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(10, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';

   -- receive - because tx side is faster than rx one, there is
   --           two clocks pause in receiving 'cause fifo is empty for a while -> therefore
   --           we wait twice for TX_WR_N signal.
   wait until TX_WR_N = '0';
   TX_RDY_N <= '0';
   wait until TX_WR_N = '1';
   TX_RDY_N <= '1';
   wait until TX_WR_N = '0';
   TX_RDY_N <= '0';
   wait until TX_WR_N = '1';
   TX_RDY_N <= '1';

-- send data
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(15, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(14, TX_DRD'length);
   wait for clkper_tx;
   TX_DRD  <= conv_std_logic_vector(13, TX_DRD'length);
   wait for clkper_tx;
   TX_DRD  <= conv_std_logic_vector(12, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';
   wait until TX_RD_N = '0';
   TX_RDY_N <= '0';
   TX_DRD  <= conv_std_logic_vector(11, TX_DRD'length);
   wait for clkper_tx;
   TX_RDY_N <= '1';
wait;
end process;

end;
