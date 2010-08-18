--
-- tsu_ptm_tb.vhd: Testbench of TSU_PTM component
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

   -- TSU signals
   signal refclk        : std_logic;
   signal clk_add       : std_logic;

   signal tsadd_init    : std_logic;
   signal tsadd_short   : std_logic;
   signal tsadd_dv      : std_logic;
   signal ts_add        : std_logic_vector(63 downto 0);

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

   signal sd            : std_logic_vector(7 downto 0);
   signal mcu           : std_logic_vector(7 downto 0);

   signal rxd_pps       : std_logic;
   signal txd_pps       : std_logic;

   -- MCU port signals
   signal mcu_rd        : std_logic;
   signal mcu_wr        : std_logic;
   signal mcu_td        : std_logic;
   signal mcu_addr      : std_logic_vector(3 downto 0);

   -- plx simulation signals
   signal plx_ctrl            : t_plx_ctrl;
   signal plx_oper            : t_plx_oper := INIT;
   signal plx_params          : t_plx_params;
   signal plx_strobe          : std_logic := '0';
   signal plx_busy            : std_logic;

   constant refclkper         : time := 100 ns; -- 10 MHz
   constant lclkfper          : time := 20 ns;  -- 50 MHz
   constant clkaddper         : time := 6.4 ns; -- 156 MHz
   constant gpsper            : time := 1000 ns;
   -- reset must be set at least 3 cycles of refclk (clk_gen)
   constant resettime         : time := 500 ns;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.TSU
port map(
      -- CLK:
      REFCLK   => refclk,
      CLK_ADD  => clk_add,
      -- Add-on card interface
      TSADD_INIT    => tsadd_init,
      TSADD_SHORT   => tsadd_short,
      TSADD_DV      => tsadd_dv,
      TS_ADD        => ts_add,
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
      USERO    => usero,
      -- MCU:
      SD       => sd,
      MCU      => mcu,
      -- GPS
      RXD_PPS  => rxd_pps,
      TXD_PPS  => txd_pps

   );

-- -------------------------------------------------------------
-- MCU port mapping
mcu(7) <= mcu_rd;
mcu(6) <= mcu_wr;
mcu(5) <= mcu_td;
mcu(4) <= '0';
mcu(3 downto 0) <= mcu_addr;

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

-- -------------------------------------------------------------
-- clk_add clock generator
clkaddgen : process
begin
   clk_add <= '1';
   wait for clkaddper/2;
   clk_add <= '0';
   wait for clkaddper/2;
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
-- RXD_PPS pulse generator (1:9)
rxdppsgen: process
begin
   rxd_pps <= '0';
   wait for (gpsper*9)/10;
   rxd_pps <= '1';
   wait for gpsper/10;
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

-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------
   variable i : integer;

begin
tsadd_init <= '0';
tsadd_short <= '0';
mcu_wr <= '0';
mcu_rd <= '0';
mcu_td <= '0';
mcu_addr <= (others => '0');
sd <= (others => 'Z');

-- local bus inicialization
plx_op(plx_init, true);

-- -------------------------------------------------------------
-- PTM initialization

-- INCR reg init
plx_op(plx_write(16#00000000#,X"00000000")); -- pci_tmp_reg
plx_op(plx_write(16#00000004#,X"00000040")); -- pci_tmp_reg
plx_op(plx_write(16#0000000C#,X"00000000")); -- pci_control_reg

-- RTR reg init
plx_op(plx_write(16#00000000#,X"FFFFFFFF")); -- pci_tmp_reg
plx_op(plx_write(16#00000004#,X"89AB00FF"));
plx_op(plx_write(16#00000008#,X"1F2F3F4F"));
plx_op(plx_write(16#0000000C#,X"00000001")); -- pci_control_reg

-- INTA reg
plx_op(plx_write(16#00000014#,X"00000001")); -- INTA reg (driven by MCU!)


-- -------------------------------------------------------------
-- TSU testing
-- -------------------------------------------------------------
tsadd_init <= '1';
wait until tsadd_dv = '1';
wait for 3.2*clkaddper;
tsadd_init <= '0';
wait for 5.1*clkaddper;

tsadd_init <= '1';
wait until tsadd_dv = '1';
wait for 3.2*clkaddper;
tsadd_init <= '0';
wait for 5.1*clkaddper;

tsadd_short <= '1';
wait until tsadd_dv = '1';
wait for 3.2*clkaddper;
tsadd_short <= '0';
wait for 5.1*clkaddper;
wait;

end process;

end architecture behavioral;
