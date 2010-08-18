--
-- crc32_64b_tb.vhd: Test bench for CRC32 module processing 64 bits in parallel
-- Copyright (C) 2006 CESNET
-- Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

entity TB_CRC32 is
end entity TB_CRC32;

architecture TB_CRC32_arch of TB_CRC32 is

constant period: time := 10 ns;

signal di: std_logic_vector(63 downto 0);
signal di_dv: std_logic;
signal eop: std_logic;
signal mask: std_logic_vector(2 downto 0);

signal clk: std_logic := '0';
signal reset: std_logic := '1';

signal c8: std_logic_vector(31 downto 0);
signal c16: std_logic_vector(31 downto 0);
signal c24: std_logic_vector(31 downto 0);
signal c32: std_logic_vector(31 downto 0);
signal c40: std_logic_vector(31 downto 0);
signal c48: std_logic_vector(31 downto 0);
signal c56: std_logic_vector(31 downto 0);
signal c64: std_logic_vector(31 downto 0);
signal crc: std_logic_vector(31 downto 0);
signal do_dv: std_logic;

signal dead : std_logic_vector(63 downto 0) := X"DEADDEADDEADDEAD";

component crc32_64b is
   port(
    DI: in std_logic_vector(63 downto 0);
    DI_DV: in std_logic;
    EOP: in std_logic;
    MASK: in std_logic_vector(2 downto 0);
    CLK: in std_logic;
    RESET: in std_logic;

    CRC: out std_logic_vector(31 downto 0);
    DO_DV: out std_logic
   );
end component;

begin

crc32_64b_instance : crc32_64b
port map(
   DI => di,
   DI_DV => di_dv,
   EOP => eop,
   MASK => mask,
   CLK => clk,
   RESET => reset,
   
   CRC => crc,
   DO_DV => do_dv
);

clk <= not clk after period / 2;

TB_proc: process

file in_file: text;
variable in_line: line;
variable data: std_logic_vector(7 downto 0);
variable good: boolean;
variable v_mask: std_logic_vector(2 downto 0) := "000";

begin

    reset    <= '1';
    di_dv    <= '0';
    eop      <= '0';
    wait until clk'event AND clk = '1';
    reset    <= '0';
    di_dv    <= '1';
    
    file_open(in_file, "test_packet.txt", READ_MODE);
    while not (endfile(in_file)) loop
        readline(in_file, in_line);
        hread(in_line, data, good);
        di(7 downto 0) <= data(7 downto 0);
        if (endfile(in_file)) then
            di(63 downto 8) <= dead(63 downto 8);
            eop <= '1';
            v_mask := "111";
        else
            readline(in_file, in_line);
            hread(in_line, data, good);
            di(15 downto 8) <= data(7 downto 0);
            if (endfile(in_file)) then
                di(63 downto 16) <= dead(63 downto 16);
                eop <= '1';
                v_mask := "110";
            else
                readline(in_file, in_line);
                hread(in_line, data, good);
                di(23 downto 16) <= data(7 downto 0);
                if (endfile(in_file)) then
                    di(63 downto 24) <= dead(63 downto 24);
                    eop <= '1';
                    v_mask := "101";
                else
                    readline(in_file, in_line);
                    hread(in_line, data, good);
                    di(31 downto 24) <= data(7 downto 0);
                    if (endfile(in_file)) then
                        di(63 downto 32) <= dead(63 downto 32);
                        eop <= '1';
                        v_mask := "100";
                    else
                        readline(in_file, in_line);
                        hread(in_line, data, good);
                        di(39 downto 32) <= data(7 downto 0);
                        if (endfile(in_file)) then
                            di(63 downto 40) <= dead(63 downto 40);
                            eop <= '1';
                            v_mask := "011";
                        else
                            readline(in_file, in_line);
                            hread(in_line, data, good);
                            di(47 downto 40) <= data(7 downto 0);
                            if (endfile(in_file)) then
                                di(63 downto 48) <= dead(63 downto 48);
                                eop <= '1';
                                v_mask := "010";
                            else
                                readline(in_file, in_line);
                                hread(in_line, data, good);
                                di(55 downto 48) <= data(7 downto 0);
                                if (endfile(in_file)) then
                                    di(63 downto 56) <= dead(63 downto 56);
                                    eop <= '1';
                                    v_mask := "001";
                                else
                                    readline(in_file, in_line);
                                    hread(in_line, data, good);
                                    di(63 downto 56) <= data(7 downto 0);
                                    if (endfile(in_file)) then
                                        eop <= '1';
                                        v_mask := "000";
                                    end if;
                                end if;
                            end if;
                        end if;
                    end if;
                end if;
            end if;
        end if;
        mask <= v_mask;
        wait for period;
    end loop;

    file_close(in_file);

    mask <= "000";
    v_mask := "000";
    di_dv <= '0';
    eop <= '0';
    wait until clk'event AND clk = '1';

    di_dv <= '1';

    file_open(in_file, "test_packet.txt", READ_MODE);
    while not (endfile(in_file)) loop
        readline(in_file, in_line);
        hread(in_line, data, good);
        di(7 downto 0) <= data(7 downto 0);
        if (endfile(in_file)) then
            di(63 downto 8) <= (others => '0');
            eop <= '1';
            v_mask := "111";
        else
            readline(in_file, in_line);
            hread(in_line, data, good);
            di(15 downto 8) <= data(7 downto 0);
            if (endfile(in_file)) then
                di(63 downto 16) <= (others => '0');
                eop <= '1';
                v_mask := "110";
            else
                readline(in_file, in_line);
                hread(in_line, data, good);
                di(23 downto 16) <= data(7 downto 0);
                if (endfile(in_file)) then
                    di(63 downto 24) <= (others => '0');
                    eop <= '1';
                    v_mask := "101";
                else
                    readline(in_file, in_line);
                    hread(in_line, data, good);
                    di(31 downto 24) <= data(7 downto 0);
                    if (endfile(in_file)) then
                        di(63 downto 32) <= (others => '0');
                        eop <= '1';
                        v_mask := "100";
                    else
                        readline(in_file, in_line);
                        hread(in_line, data, good);
                        di(39 downto 32) <= data(7 downto 0);
                        if (endfile(in_file)) then
                            di(63 downto 40) <= (others => '0');
                            eop <= '1';
                            v_mask := "011";
                        else
                            readline(in_file, in_line);
                            hread(in_line, data, good);
                            di(47 downto 40) <= data(7 downto 0);
                            if (endfile(in_file)) then
                                di(63 downto 48) <= (others => '0');
                                eop <= '1';
                                v_mask := "010";
                            else
                                readline(in_file, in_line);
                                hread(in_line, data, good);
                                di(55 downto 48) <= data(7 downto 0);
                                if (endfile(in_file)) then
                                    di(63 downto 56) <= (others => '0');
                                    eop <= '1';
                                    v_mask := "001";
                                else
                                    readline(in_file, in_line);
                                    hread(in_line, data, good);
                                    di(63 downto 56) <= data(7 downto 0);
                                    if (endfile(in_file)) then
                                        eop <= '1';
                                        v_mask := "000";
                                    end if;
                                end if;
                            end if;
                        end if;
                    end if;
                end if;
            end if;
        end if;
        mask <= v_mask;
        wait for period;
    end loop;

    file_close(in_file);
    
    mask <= "000";
    v_mask := "000";
    di_dv <= '0';
    eop <= '0';
    wait until do_dv = '1';
    wait;

end process;

end architecture TB_CRC32_arch;

