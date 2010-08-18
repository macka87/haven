-- testbench.vhd: frame link stat unit testbench
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

library work;

use work.lb_pkg.all;
use work.ib_sim_oper.all;  -- Internal bus simulation pkg

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
constant reset_delay :time := 50 ns;

constant IFCS_CONST : integer := 5;

constant STATE_REG   : std_logic_vector(31 downto 0) := X"00000000";
constant CLK_CNT_L   : std_logic_vector(31 downto 0) := X"00000008";
constant CLK_CNT_H   : std_logic_vector(31 downto 0) := X"0000000C";
constant SRC_CNT0_L  : std_logic_vector(31 downto 0) := X"00000010";
constant SRC_CNT0_H  : std_logic_vector(31 downto 0) := X"00000014";
constant DST_CNT0_L  : std_logic_vector(31 downto 0) := X"00000020";
constant DST_CNT0_H  : std_logic_vector(31 downto 0) := X"00000024";
constant BOTH_CNT0_L : std_logic_vector(31 downto 0) := X"00000030";
constant BOTH_CNT0_H : std_logic_vector(31 downto 0) := X"00000034";
constant SRC_CNT1_L  : std_logic_vector(31 downto 0) := X"00000050";
constant SRC_CNT1_H  : std_logic_vector(31 downto 0) := X"00000054";
constant DST_CNT1_L  : std_logic_vector(31 downto 0) := X"00000060";
constant DST_CNT1_H  : std_logic_vector(31 downto 0) := X"00000064";
constant BOTH_CNT1_L : std_logic_vector(31 downto 0) := X"00000070";
constant BOTH_CNT1_H : std_logic_vector(31 downto 0) := X"00000074";
constant SRC_CNT2_L  : std_logic_vector(31 downto 0) := X"00000090";
constant SRC_CNT2_H  : std_logic_vector(31 downto 0) := X"00000094";
constant DST_CNT2_L  : std_logic_vector(31 downto 0) := X"000000A0";
constant DST_CNT2_H  : std_logic_vector(31 downto 0) := X"000000A4";
constant BOTH_CNT2_L : std_logic_vector(31 downto 0) := X"000000B0";
constant BOTH_CNT2_H : std_logic_vector(31 downto 0) := X"000000B4";
constant SRC_CNT3_L  : std_logic_vector(31 downto 0) := X"000000D0";
constant SRC_CNT3_H  : std_logic_vector(31 downto 0) := X"000000D4";
constant DST_CNT3_L  : std_logic_vector(31 downto 0) := X"000000E0";
constant DST_CNT3_H  : std_logic_vector(31 downto 0) := X"000000E4";
constant BOTH_CNT3_L : std_logic_vector(31 downto 0) := X"000000F0";
constant BOTH_CNT3_H : std_logic_vector(31 downto 0) := X"000000F4";
constant SRC_CNT4_L  : std_logic_vector(31 downto 0) := X"00000110";
constant SRC_CNT4_H  : std_logic_vector(31 downto 0) := X"00000114";
constant DST_CNT4_L  : std_logic_vector(31 downto 0) := X"00000120";
constant DST_CNT4_H  : std_logic_vector(31 downto 0) := X"00000124";
constant BOTH_CNT4_L : std_logic_vector(31 downto 0) := X"00000130";
constant BOTH_CNT4_H : std_logic_vector(31 downto 0) := X"00000134";

signal clk    : std_logic := '0';
signal reset  : std_logic;

-- I/O MI32 SW interface
signal dwr    : std_logic_vector(31 downto 0);    -- Input Data
signal addr   : std_logic_vector(31 downto 0);    -- Address
signal rd     : std_logic;                        -- Read Request
signal wr     : std_logic;                        -- Write Request
signal be     : std_logic_vector(3 downto 0);     -- Byte Enable
signal drd    : std_logic_vector(31 downto 0);   -- Output Data
signal ardy   : std_logic;                       -- Address Ready
signal drdy   : std_logic;                       -- Data Ready

signal src_rdy_n  : std_logic_vector(IFCS_CONST - 1 downto 0) := "10101"; --(others => '1');
signal dst_rdy_n  : std_logic_vector(IFCS_CONST - 1 downto 0) := "01010"; --(others => '0');

-- mi32 bus interface
signal mi32             : t_mi32;

-- mi32 simulation signals
signal mi32_sim_ctrl    : t_ib_ctrl;
signal mi32_sim_strobe  : std_logic := '0';
signal mi32_sim_busy    : std_logic;

begin

uut : entity work.fl_stat_64
   generic map(
      IFCS              => IFCS_CONST        -- number of fl pairs of devices under control, at least one
   )
   port map(
      CLK               => clk,
      RESET             => reset,

      -- In / Out SW interface via MI_32
      DWR               => mi32.dwr,         -- Input data
      ADDR              => mi32.addr,        -- Address
      RD                => mi32.rd,          -- Read Request
      WR                => mi32.wr,          -- Write Request
      BE                => mi32.be,          -- Byte Enable
      DRD               => mi32.drd,         -- Output Data
      ARDY              => mi32.ardy,        -- Address Ready
      DRDY              => mi32.drdy,        -- Data Ready

      -- FrameLink stats counter
      SRC_RDY_N   => src_rdy_n,
      DST_RDY_N   => dst_rdy_n
   );

-- -------------------------------------------------------------------------
--                   MI32 Simulation Component
-- -------------------------------------------------------------------------
mi32_sim_u: entity work.mi32_sim
   generic map(
      UPSTREAM_LOG_FILE   => "", --"./data/mi32upstream",
      DOWNSTREAM_LOG_FILE => "", --"./data/mi32downstream",
      BASE_ADDR           => X"00000000",
      LIMIT               => X"00000100",
      FREQUENCY           => LOCAL_BUS_FREQUENCY,
      BUFFER_EN           => false
     )

   port map(
      -- Common interface
      IB_RESET          => reset,
      IB_CLK            => clk,

      -- User Component Interface
      CLK               => clk,
      MI32.DWR          => mi32.dwr,
      MI32.ADDR         => mi32.addr,
      MI32.RD           => mi32.rd,
      MI32.WR           => mi32.wr,
      MI32.BE           => mi32.be,
      MI32.DRD          => mi32.drd,
      MI32.ARDY         => mi32.ardy,
      MI32.DRDY         => mi32.drdy,

      -- IB SIM interface
      STATUS            => open,
      CTRL              => mi32_sim_ctrl,
      STROBE            => mi32_sim_strobe,
      BUSY              => mi32_sim_busy
  );

-- ----------------------------------------------------
-- CLK generator - 100 MHz
clk_gen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process clk_gen;

src_dst_gen : for i in 0 to IFCS_CONST - 1 generate
   src_rdy_n(i) <= not src_rdy_n(i) after (i+1)*(clkper + 10 ps);
   dst_rdy_n(i) <= not dst_rdy_n(i) after 6*(i+1)*(clkper + 10 ps);
end generate;

-- ----------------------------------------------------
-- Reset generation
proc_reset : process
begin
   reset <= '1';
   wait for reset_delay;
   reset <= '0';
   wait;
end process proc_reset;
      
-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
testbench_stat_unit : process
   -- ----------------------------------------------------------------
   --                    Procedures declaration
   -- ----------------------------------------------------------------

   -- This procedure must be placed in this testbench file. Using this
   -- procedure is necessary for correct function of MI32_SIM
   procedure ib_op(ctrl : in t_ib_ctrl) is
      begin
         wait until (CLK'event and CLK='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (CLK'event and CLK='1');
         mi32_sim_strobe <= '0';
      end ib_op;

    -- ----------------------------------------------------------------
    --                        Testbench Body
    -- ----------------------------------------------------------------
begin
   wait for reset_delay;

   -- test zapisu do registru
   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000009")); -- cnt enable

   wait for 30*clkper;

   -- test cteni z registru
   ib_op(ib_local_read(CLK_CNT_L, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(CLK_CNT_H, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(SRC_CNT0_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(SRC_CNT0_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT0_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT0_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT0_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT0_H, X"11111111", 4, 16#ABAF#));

   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000009")); -- cnt enable

   wait for 20*clkper;

   ib_op(ib_local_read(STATE_REG, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(SRC_CNT1_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(SRC_CNT1_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT1_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT1_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT1_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT1_H, X"11111111", 4, 16#ABAF#));

   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000009")); -- cnt enable

   wait for 20*clkper;

   ib_op(ib_local_read(SRC_CNT2_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(SRC_CNT2_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT2_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT2_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT2_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT2_H, X"11111111", 4, 16#ABAF#));

   wait for 20*clkper;

   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000002")); -- reset counters

   wait for 20*clkper;

   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000009")); -- cnt enable

   wait for 30*clkper;

   ib_op(ib_local_read(STATE_REG, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(CLK_CNT_L, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(CLK_CNT_H, X"11111111", 4, 16#ABAE#));
   ib_op(ib_local_read(SRC_CNT3_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(SRC_CNT3_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT3_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT3_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT3_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT3_H, X"11111111", 4, 16#ABAF#));

   ib_op(ib_local_write(STATE_REG, X"11111111", 1, 16#ABAC#, '0', X"0000000000000009")); -- cnt enable

   wait for 20*clkper;

   ib_op(ib_local_read(SRC_CNT4_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(SRC_CNT4_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT4_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(DST_CNT4_H, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT4_L, X"11111111", 4, 16#ABAF#));
   ib_op(ib_local_read(BOTH_CNT4_H, X"11111111", 4, 16#ABAF#));

   wait for 300*clkper;
end process;

end;
