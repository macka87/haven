--
-- i2c_master_tb.vhd: Testbench for i2c master unit
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity i2c_master_tb is
end entity i2c_master_tb;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of i2c_master_tb is

   constant clkper: time := 10 ns;

   signal reset   : std_logic;

   signal clk     : std_logic;
   
   signal dev     : std_logic_vector(6 downto 0); -- device address
   signal addr    : std_logic_vector(7 downto 0); -- data word adress
   signal rw      : std_logic; -- read/write
   signal en      : std_logic; -- enable
   signal data    : std_logic_vector(7 downto 0);
   signal di      : std_logic_vector(7 downto 0);
   signal do      : std_logic_vector(7 downto 0); -- valid when op_done asserted
   signal op_ok   : std_logic;
   signal op_done : std_logic;
   signal test    : std_logic;

   -- I2C interface
   signal scl     : std_logic;
   signal scl_m     : std_logic;
   signal sda     : std_logic;
   signal sda_m     : std_logic;

   signal scl_s     : std_logic; -- slave
   signal sda_s     : std_logic; -- slave

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

-- ----------------------------------------------------
-- UUT mapping
-- ----------------------------------------------------

-- I2C_MASTER instantination
UUT : entity work.i2c_master
port map (
   RESET   => RESET,
   CLK     => CLK,
      
   DEV     => dev,
   ADDR    => addr,
   RW      => rw,
   EN      => en,
      
   DI      => di,
   DO      => do,
   OP_OK   => op_ok,
   OP_DONE => op_done,
   
   SCL_I     => scl,
   SCL_O     => scl_m,
   SDA_I     => sda,
   SDA_O     => sda_m
);


-- ----------------------------------------------------------------------------
-- clock generator
clk_clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

in_p : process

begin
   dev  <= (others=>'0');
   addr <= (others=>'0');
   di   <= (others=>'0');
   rw   <= '0';
   en   <= '0';

   reset <= '1';
   wait for 100 ns;
   reset <= '0';

   -- at first we will try to write something
   wait until (clk='1' and clk'event);
   dev  <= "1010111";
   addr <= "10101111";
   di   <= "10101011";
   rw   <= '0'; -- write operation
   en   <= '1';
   wait until (clk='1' and clk'event);
   dev  <= (others=>'0');
   addr <= (others=>'0');
   di   <= (others=>'0');
   rw   <= '0';
   en   <= '0';

   -- then try to read something
   wait until (clk='1' and clk'event and op_done='1');
   dev  <= "1010111";
   addr <= "00000000";
   di   <= "00000000";
   rw   <= '1'; -- read operation
   en   <= '1';

   wait until (clk='1' and clk'event);
   dev  <= (others=>'0');
   addr <= (others=>'0');
   di   <= (others=>'0');
   rw   <= '0';
   en   <= '0';
   
   -- try to assert en, when busy
   wait;
end process;

i2c_p : process
begin
   scl_s <= '1';
   sda_s <= '1';
   test <= '0';

   wait until reset='0';

   -- ------ Byte write -------------------------------------------------------
   wait until (scl='1' and sda'event and sda='0'); -- start command
   
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');

   wait for 7.5 us; -- master waiting for ack device address
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';

   wait until (scl'event and scl='1'); -- write address
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');

   wait for 7.5 us; -- master waiting for ack write address ack
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';

   -- store data from master
   wait until (scl'event and scl='1'); data(7) <= sda;
   wait until (scl'event and scl='1'); data(6) <= sda;
   wait until (scl'event and scl='1'); data(5) <= sda;
   wait until (scl'event and scl='1'); data(4) <= sda;
   wait until (scl'event and scl='1'); data(3) <= sda;
   wait until (scl'event and scl='1'); data(2) <= sda;
   wait until (scl'event and scl='1'); data(1) <= sda;
   wait until (scl'event and scl='1'); data(0) <= sda;

   wait for 7.5 us; -- master waiting for ack data
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';
   
   wait until (scl='1' and sda'event and sda='1'); -- stop command
   
   -- ------ random read ------------------------------------------------------
   wait until (scl='1' and sda'event and sda='0'); -- start command
   
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');

   wait for 7.5 us; -- master waiting for ack device address
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';

   wait until (scl'event and scl='1'); -- write address
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');

   wait for 7.5 us; -- master waiting for ack write address ack
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';
   
   test <= '1';
   wait until (scl='1' and sda'event and sda='0'); -- start command
   test <= '0';
   -- device address
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   wait until (scl'event and scl='1');
   
   wait for 7.5 us; -- master waiting for ack device address
   sda_s <= '0';
   wait for 10 us;
   sda_s <= '1';

   wait until (scl'event and scl='1'); sda_s <= data(7);
   wait until (scl'event and scl='1'); sda_s <= data(6);
   wait until (scl'event and scl='1'); sda_s <= data(5);
   wait until (scl'event and scl='1'); sda_s <= data(4);
   wait until (scl'event and scl='1'); sda_s <= data(3);
   wait until (scl'event and scl='1'); sda_s <= data(2);
   wait until (scl'event and scl='1'); sda_s <= data(1);
   wait until (scl'event and scl='1'); sda_s <= data(0);
   wait for 7.5 us; -- waiting for ack for continuation (no ack will be performed)
   sda_s <= '1';
   wait for 10 us;

   wait until (scl='1' and sda'event and sda='1'); -- stop command
   
   -- try to not ack device address, word address, or data...
   wait;
end process;

sda <= sda_m and sda_s;
scl <= scl_m and scl_s;

--pullup_sda_p : process
--begin
--   if (sda_m='1' and sda_s='1') then
--      sda <= '1';
--   else
--      sda <= '0';
--   end if;
--end process;

--pullup_scl_p : process
--begin
--   if (scl_m='1' and scl_s='1') then
--      scl <= '1';
--   else
--      scl <= '0';
--   end if;
--end process;

end architecture behavioral;
