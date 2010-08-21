--
-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2007 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
--            Pus Viktor <xpusvi00@stud.fit.vutbr.cz>
--            Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity;

-- ----------------------------------------------------------------------------
--                         Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH : integer := 32;
   constant TEST_ITEMS : integer := 16;
   constant clkper     : time := 20 ns;

   signal clk        : std_logic;
   signal reset      : std_logic;

   signal wr         : std_logic;
   signal di         : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal blk_end    : std_logic;
   signal wr_discard : std_logic;

   signal rd         : std_logic;
   signal do         : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal dv         : std_logic;
   signal blk_ready  : std_logic;
   signal blk_finish : std_logic;
   signal rd_discard : std_logic;

   signal full       : std_logic;
   signal empty      : std_logic;
   signal status     : std_logic_vector(log2(TEST_ITEMS) downto 0);

-- ----------------------------------------------------------------------------
--                           Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.FIFO_SYNC_BLOCK
generic map(
    MAIN_MEM   => BRAM,
    ADDR_MEM   => LUT,
    LATENCY    => 1,
    ITEMS      => TEST_ITEMS,
    ITEM_WIDTH => TEST_WIDTH,
    BLOCK_TYPE => variable_size,
    BLOCK_SIZE => 4,
    MAX_BLOCKS => TEST_ITEMS,
    DISCARD    => WriteReadDiscard,
    PREFETCH   => false
)
port map(
   CLK        => clk,
   RESET      => reset,

   -- Write interface
   WR         => wr,
   DI         => di,
   BLK_END    => blk_end,
   WR_DISCARD => wr_discard,

   -- Read interface
   RD         => rd,
   DO         => do,
   DO_DV      => dv,
   BLK_READY  => blk_ready,
   BLK_FINISH => blk_finish,
   RD_DISCARD => rd_discard,

   -- Info
   FULL       => full,
   EMPTY      => empty,
   STATUS     => status
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
--                              Testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
  reset      <= '1';
  rd         <= '0';
  wr         <= '0';
  di         <= (others => '0');
  blk_end    <= '0';
  rd_discard <= '0';
  wr_discard <= '0';

  wait for 4*clkper;
  reset <= '0';

  wait for 8*clkper;

  -- fill fifo
  wr <= '1';
  for i in 1 to 20 loop
    di <= conv_std_logic_vector(i, di'length);
    if ((i = 8) or (i = 15)) then
      blk_end <= '1';
    else
      blk_end <= '0';
    end if;

    -- do write discard
    if (i = 13) then
      wr_discard <= '1';
    else
      wr_discard <= '0';
    end if;

    wait for clkper;
  end loop;
  wr <= '0';

  wait for 10*clkper;

  -- empty fifo
  rd <= '1';
  wait for 6*clkper;

  -- do read discard
  rd_discard <= '1';
  wait for clkper;
  rd_discard <= '0';

  wait for 20*clkper;
  rd <= '0';

  wait for 8*clkper;

  -- fill fifo, in the middle start reading
  wr <= '1';
  for i in 1 to 20 loop
    di <= conv_std_logic_vector(i, di'length);
    if ((i = 8) or (i = 12) or (i = 20)) then
      blk_end <= '1';
    else
      blk_end <= '0';
    end if;
    if (i = 8) then
      rd <= '1';
    end if;

    -- do both discards
    if (i = 13) then
      wr_discard <= '1';
      rd_discard <= '1';
    else
      wr_discard <= '0';
      rd_discard <= '0';
    end if;

    wait for clkper;
  end loop;

  wr <= '0';
  blk_end <= '0';
  wait for 10*clkper;
  rd <= '0';

  -- last test
  wr <= '1';
  for i in 1 to 10 loop
    di <= conv_std_logic_vector(i, di'length);
    if (i = 8) then
      blk_end <= '1';
    else
      blk_end <= '0';
    end if;
    if (i = 8) then
      rd <= '1';
    end if;
    wait for clkper;
  end loop;

  wr <= '0';
  wait for 4*clkper;
  wr <= '1';

  for i in 11 to 20 loop
    di <= conv_std_logic_vector(i, di'length);
    if ((i = 12) or (i = 20)) then
      blk_end <= '1';
    else
      blk_end <= '0';
    end if;
    if (i = 14) then
      rd <= '0';
    end if;
    if (i = 18) then
      rd <= '0';
    end if;
    wait for clkper;
  end loop;

  wr <= '0';
  blk_end <= '0';
  wait for 2*clkper;
  rd <= '0';
  wait for 2*clkper;
  rd <= '1';
  wait;
end process;

-- ----------------------------------------------------------------------------
end architecture;
