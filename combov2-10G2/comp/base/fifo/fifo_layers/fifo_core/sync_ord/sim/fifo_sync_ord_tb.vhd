-- fifo_sync_ord_tb.vhd: Testbench of the fifo_sync_ord component
-- Copyright (C) 2007 CESNET
-- Author: Jan Koritak <jenda@liberouter.org>
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


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;
use work.fifo_pkg.all;
entity testbench is

end testbench;

architecture behavioral of testbench is

    --Constant for memory settings
    constant ItemCount   : integer := 8;
    constant ItemSize    : integer := 16;
    constant lat         : integer := 1;  --Tested latency

    --Signals
    signal reset         : std_logic;
    signal clk           : std_logic;
    signal WriteEn       : std_logic;
    signal DataIn        : std_logic_vector(ItemSize-1 downto 0);
    signal ReadEn        : std_logic;
    signal DataOut       : std_logic_vector(ItemSize-1 downto 0);
    signal DataValid     : std_logic;
    signal Empty         : std_logic;
    signal Full          : std_logic;
    signal Status        : std_logic_vector(log2(ItemCount) downto 0);

    --Constant for tesbench
    constant period      : time := 20 ns; --Clock period
    constant reset_time  : time := 100 ns; --Reset duration

    begin

    --Generating reset
    Reset_gen : process
    begin
    reset <= '1';
    wait for reset_time;
    reset <= '0';
    wait;
    end process;

    --Generating clocks
    clk_gen : process 
    begin
        clk <= '1';
        wait for period/2;
        clk <= '0';
        wait for period/2;
    end process clk_gen;

    --Importing FIFO memory
    uut : entity work.fifo_sync_ord
        generic map (
            items => ItemCount,
            item_width =>ItemSize,
            latency =>lat,
            mem_type => BRAM,
            prefetch => true
        )
        port map (
            CLK => clk,
            WR => WriteEn,
            DI => DataIn,

            RD =>ReadEn,
            DO =>DataOut,
            DO_DV => DataValid,

            EMPTY => Empty,
            FULL => Full,
            STATUS => Status,

            RESET => reset

        );

    -- Testing FIFO
    test : process
    begin

        -- Initializing signals
        WriteEn <= '0';
        DataIn <= X"0000";
        ReadEn <= '0';
        
        -- Adding a bunch of items
        wait for 120 ns;
        DataIn <= X"0123";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';
--wait;
        wait for 40 ns;
        DataIn <= X"1234";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';

        wait for 40 ns;
        DataIn <= X"2345";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';

        -- Simultaneous reading and writing
        wait for 40 ns;
        DataIn <= X"3456";
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        WriteEn <= '1';
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        WriteEn <= '0';
        ReadEn <= '0';

        wait for 40 ns;
        DataIn <= X"4567";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';

        wait for 40 ns;
        DataIn <= X"5678";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';
        
        wait for 40 ns;
        DataIn <= X"6789";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';
        
        wait for 40 ns;
        DataIn <= X"789A";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';

        wait for 40 ns;
        DataIn <= X"89AB";
        wait for 20 ns;
        WriteEn <= '1';
        wait for 20 ns;
        WriteEn <= '0';

        -- Reading all the items
        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';

        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        --wait for 40 ns;
        --wait until clk = '1' and clk'event;
        --ReadEn <= '1';
        --wait for 20 ns;
        --wait until clk = '1' and clk'event;
        --ReadEn <= '0';


        -- Simultaneous reading and writing
        -- on epmty fifo
        wait for 40 ns;
        DataIn <= X"FFFF";
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        WriteEn <= '1';
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        WriteEn <= '0';
        ReadEn <= '0';

        wait for 40 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '1';
        wait for 20 ns;
        wait until clk = '1' and clk'event;
        ReadEn <= '0';

        wait;
    end process test;
end architecture;
