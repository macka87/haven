--
-- tsu2pci_tb.vhd: Testbench of TSU2PCI component
-- Copyright (C) 2005 CESNET
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
use work.plx_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- testbench signals
   signal ts_req        : std_logic_vector(7 downto 0);
   signal ts_fast       : std_logic_vector(7 downto 0);

   -- PTM ifc signals
   signal refclk        : std_logic;
   signal ts            : std_logic_vector(7 downto 0);
   signal ts_dv         : std_logic;
   signal ts_init       : std_logic;
   signal ts_short      : std_logic;
   signal ppfts         : std_logic;

   -- PLX
   signal lclkf         : std_logic;
   signal lad           : std_logic_vector(31 downto 0);
   signal lholda        : std_logic;
   signal ads           : std_logic;
   signal lframe        : std_logic;
   signal lint          : std_logic;
   signal lbe           : std_logic_vector(3 downto 0);
   signal blast         : std_logic;
   signal lwr           : std_logic;
   signal ready         : std_logic;
   signal lhold         : std_logic;
   signal lreset        : std_logic;
   signal usero         : std_logic;

   -- plx simulation signals
   signal plx_ctrl            : t_plx_ctrl;
   signal plx_oper            : t_plx_oper := INIT;
   signal plx_params          : t_plx_params;
   signal plx_strobe          : std_logic := '0';
   signal plx_busy            : std_logic;

   constant refclkper         : time := 12.5 ns;-- 80 MHz
   constant lclkfper          : time := 20 ns;  -- 50 MHz
   -- reset must be set at least 3 cycles of refclk (clk_gen)
   constant resettime         : time := 500 ns;

   constant shift             : time := 0 ns;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.FPGA
port map(
      -- IO interface
      IO(51 downto 44)  => "ZZZZZZZZ",
      IO(43)            => ts(7),
      IO(42)            => ts(5),
      IO(41)            => ts(3),
      IO(40)            => ts(1),
      IO(39)            => ppfts,
      IO(38 downto 37)  => "00",
      IO(36)            => ts_short,
      IO(35)            => ts(6),
      IO(34)            => ts(4),
      IO(33)            => ts(2),
      IO(32)            => ts(0),
      IO(31)            => ts_dv,
      IO(30)            => '0',
      IO(29)            => ts_init,
      IO(28)            => refclk,
      IO(27 downto 0)   => "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZ",
      -- PLX:
      LCLKF    => lclkf,
      LAD      => lad,
      LHOLDA   => lholda,
      ADS      => ads,
      BLAST    => blast,
      LWR      => lwr,
      READY    => ready,
      LHOLD    => lhold,
      LRESET   => lreset,
      USERO    => usero
   );

-- -------------------------------------------------------------
-- lclkf clock generator
lclkfgen : process
begin
   lclkf <= '1';
   wait for lclkfper/2;
   lclkf <= '0';
   wait for lclkfper/2;
end process;

-- -------------------------------------------------------------
-- refclk clock generator
refclkgen : process
begin
   refclk <= '1';
   wait for refclkper/2;
   refclk <= '0';
   wait for refclkper/2;
end process;

-- ----------------------------------------------------
-- Reset generation
proc_reset : process
begin
   lreset <= '0';
   wait for resettime;
   lreset <= '1';
   wait;
end process;

-- -------------------------------------------------------------
-- PLX Simulation component
PLX_SIM_U : entity work.plx_sim
generic map(
   PLX_HOLD       => 10 ns,
   DEBUG_REPORT   => false
)
port map(
   -- PLX interface
   LCLKF       => lclkf,
   LAD         => lad,
   LBE         => lbe,
   LHOLDA      => lholda,
   LFRAME      => lframe,
   ADS         => ads,
   BLAST       => blast,
   LWR         => lwr,
   READY       => ready,
   LHOLD       => lhold,
   LINT        => lint,
   LRESET      => open,
   USERO       => usero,

   -- Simulation interface
   OPER        => plx_oper,
   PARAMS      => plx_params,
   STROBE      => plx_strobe,
   BUSY        => plx_busy
);

tsu_fast: process

   variable i : integer := 0;
   variable j : integer := 255;

begin
      wait until refclk = '1';
      wait for shift;
      while true loop
         ts_fast <= conv_std_logic_vector(i*j,8);
         i := i + 1;
         j := j - 1;
         wait for refclkper+shift;
      end loop;
end process tsu_fast;

with ts_dv select
   ts <= ts_req when '1',
         ts_fast when others;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

tb : process


-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

-- ----------------------------------------------------------------
-- Procedure plx_op performs plx operation specified
-- in data structure t_plx_ctrl
--
-- Parameters:
--       ctrl        - structure for plx controling
--       block_wait  - block waiting
--
procedure plx_op(ctrl : in t_plx_ctrl; block_wait : in boolean := false) is
begin
   wait until (LCLKF'event and LCLKF='1' and plx_busy = '0');
   wait for 0.1*lclkfper;
   plx_oper    <= ctrl.oper;
   plx_params  <= ctrl.params;
   plx_strobe  <= '1';

   wait for lclkfper;
   plx_strobe  <= '0';

   -- block waiting, if reguired
   if (block_wait) then
      wait until (LCLKF'event and LCLKF='1' and plx_busy = '0');
   end if;
end plx_op;

procedure tsu_init_req(data: in std_logic_vector(63 downto 0)) is
begin
   plx_op(plx_write(16#00000008#,X"00000001")); -- pci_tmp_reg
   wait for 10*lclkfper;
   wait until refclk = '1';
   wait for shift;
   ts_dv <= '1';
   for i in 8 downto 1 loop
      ts_req <= data(i*8-1 downto (i-1)*8);
      wait for refclkper+shift;
   end loop;
   ts_dv <= '0';
end tsu_init_req;

procedure tsu_short_req(data: in std_logic_vector(7 downto 0)) is
begin
   plx_op(plx_write(16#00000008#,X"00000001")); -- pci_tmp_reg
   wait for 10*lclkfper;
   wait until refclk = '1';
   wait for shift;
   ts_dv <= '1';
   ts_req <= data;
   wait for refclkper+shift;
   ts_dv <= '0';
end tsu_short_req;


-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------
   variable i : integer;

begin
-- signal init
ts_dv <= '0';
ts_req<= "00000000";
ppfts <= '0';

-- local bus inicialization
plx_op(plx_init, true);

-- -------------------------------------------------------------
-- TSU2PCI design testing
-- -------------------------------------------------------------
tsu_init_req(X"0123456789ABCDEF");
tsu_init_req(X"13579BDF02468ACE");

plx_op(plx_read(16#00000000#));
plx_op(plx_read(16#00000004#));

wait;

end process;

end architecture behavioral;
