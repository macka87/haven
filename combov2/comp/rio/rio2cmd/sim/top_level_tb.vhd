--
-- ope_tb.vhd: Testbench of RIO2CMD component
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- clock signals
   signal refclk     : std_logic;
   signal usrclk     : std_logic;
   signal usrclk2    : std_logic;
   signal cmdclk     : std_logic;
   signal reset      : std_logic;

   -- CMD TX signals
   signal di         : std_logic_vector(31 downto 0);
   signal di_cmd     : std_logic_vector(3 downto 0);
   signal di_dv      : std_logic;
   signal di_full    : std_logic;

   -- CMD RX signals
   signal do         : std_logic_vector(31 downto 0);
   signal do_cmd     : std_logic_vector(3 downto 0);
   signal do_dv      : std_logic;
   signal do_full    : std_logic;

   -- RIO signals
   signal txn        : std_logic;
   signal txp        : std_logic;
   signal rxp        : std_logic;
   signal rxn        : std_logic;

   constant refclkper   : time := 8 ns;
   constant usrclkper   : time := 8 ns;
   constant cmdclkper   : time := 10 ns;

   constant data_file1  : string := "../data/cmd_data1.txt";
   constant data_file2  : string := "../data/cmd_data2.txt";

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------

begin
uut : entity work.rio2cmd
generic map(
      LOOPBACK       => "10" -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      )
port map(
      -- Common Interface
      RESET          => reset,
      REFCLK         => refclk,
      USRCLK         => usrclk,
      USRCLK2        => usrclk2,
      CMDCLK         => cmdclk,

      -- Command Protocol TX Interface
      DI             => di,
      DI_CMD         => di_cmd,
      DI_DV          => di_dv,
      DI_FULL        => di_full,

      -- Command Protocol RX Interface
      DO             => do,
      DO_CMD         => do_cmd,
      DO_DV          => do_dv,
      DO_FULL        => do_full,

      -- MGT Interface
      RXN            => rxn,
      RXP            => rxp,
      TXN            => txn,
      TXP            => txp
   );

-- ----------------------------------------------------
-- refclk clock generator
refclkgen : process
begin
   refclk <= '1';
   wait for refclkper/2;
   refclk <= '0';
   wait for refclkper/2;
end process;

-- cmdclk clock generator
cmdclkgen : process
begin
   cmdclk <= '1';
   wait for cmdclkper/2;
   cmdclk <= '0';
   wait for cmdclkper/2;
end process;

-- usrclk clock generator
usrclkgen : process
begin
   usrclk <= '1';
   wait for usrclkper/2;
   usrclk <= '0';
   wait for usrclkper/2;
end process;

-- usrclk2 clock generator
usrclk2gen : process (reset, usrclk)
begin
   if (reset'event and reset = '1') then
      usrclk2 <= '0';
   elsif (usrclk'event and usrclk = '0') then
      usrclk2 <= not usrclk2;
   end if;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

tb : process

-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------

   file infile: text;
   variable l : line;
   variable d : std_logic_vector(31 downto 0);
   variable k : std_logic_vector(3 downto 0);
   variable good : boolean;
   
begin
di <= (others => '0');
di_cmd <= "0000";
di_dv <= '0';
do_full <= '0';

reset <= '1';
wait for 10 us;
reset <= '0';


      -- process cmd_file
      wait for 20*cmdclkper;
      file_open(infile,data_file1,READ_MODE);
      di_dv <= '1';
      readline(infile,l);
      hread(l,d,good);
      readline(infile,l);
      hread(l,k,good);
      di <= d;
      di_cmd <= k;
      wait for cmdclkper;
      while not (endfile(infile)) loop
         readline(infile,l);
         hread(l,d,good);
         readline(infile,l);
         hread(l,k,good);
         di <= d;
         di_cmd <= k;
         wait for cmdclkper;
      end loop;
      di_dv <= '0';
      file_close(infile);

      -- process cmd_file
      wait for 20*cmdclkper;
      file_open(infile,data_file1,READ_MODE);
      di_dv <= '1';
      readline(infile,l);
      hread(l,d,good);
      readline(infile,l);
      hread(l,k,good);
      di <= d;
      di_cmd <= k;
      wait for cmdclkper;
      while not (endfile(infile)) loop
         readline(infile,l);
         hread(l,d,good);
         readline(infile,l);
         hread(l,k,good);
         di <= d;
         di_cmd <= k;
         wait for cmdclkper;
      end loop;
      di_dv <= '0';
      file_close(infile);

wait;


end process;

end architecture behavioral;
