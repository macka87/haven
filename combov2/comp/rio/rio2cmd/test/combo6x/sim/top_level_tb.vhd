--
-- ope_tb.vhd: Testbench of RIO test component
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
use work.plx_oper.all;

use work.addr_space.all;
use work.constants.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- bus signals
   signal x          : std_logic_vector(39 downto 0);

   -- clock signals
   signal lclkf      : std_logic;
   signal clkf       : std_logic;

   -- IOS signals
   signal ios        : std_logic_vector(103 downto 0);

   -- RIO signals
   signal txn3       : std_logic;
   signal txp3       : std_logic;
   signal rxp3       : std_logic;
   signal rxn3       : std_logic;
   signal txn2       : std_logic;
   signal txp2       : std_logic;
   signal rxp2       : std_logic;
   signal rxn2       : std_logic;
   signal txn1       : std_logic;
   signal txp1       : std_logic;
   signal rxp1       : std_logic;
   signal rxn1       : std_logic;
   signal txn0       : std_logic;
   signal txp0       : std_logic;
   signal rxp0       : std_logic;
   signal rxn0       : std_logic;

   -- plx simulation signals
   signal plx_ctrl            : t_plx_ctrl;
   signal plx_status          : t_plx_status;
   signal plx_oper            : t_plx_oper := INIT;
   signal plx_params          : t_plx_params;
   signal plx_strobe          : std_logic := '0';
   signal plx_busy            : std_logic;

   -- PLX signals ---------------------------------------------------
   alias lad0   : std_logic_vector(26 downto  0) is x(26 downto  0);
   alias lad1   : std_logic_vector(31 downto 27) is x(32 downto 28);
   alias lhold  : std_logic                      is x(34);
   alias lwr    : std_logic                      is x(35);
   alias ready  : std_logic                      is x(36);
   alias blast  : std_logic                      is x(37);
   alias ads    : std_logic                      is x(38);

   signal lholda : std_logic; -- FIXME

   constant PLX_HOLD       : time := 10 ns;
   constant DEBUG_REPORT   : boolean := false;
   constant RESET_DELAY    : time := 10 us;

   constant clkper      : time := 20 ns;
   constant clkfper     : time := 8 ns; -- 125 MHz

   constant data_file1  : string := "../../../data/cmd_data1.txt";
   constant data_file2  : string := "../../../data/cmd_data2.txt";

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
uut : entity work.fpga_u5
port map(
      -- CLK:
      LCLKF     => lclkf,
      LVDSFP    => '0',
      LVDSFN    => '0',
      CLKF      => clkf,
      -- IO
      X         => x,
      IOS       => ios,
      -- RIO
      TXN3      => txn3,
      TXP3      => txp3,
      RXP3      => rxp3,
      RXN3      => rxn3,
      TXN2      => txn2,
      TXP2      => txp2,
      RXP2      => rxp2,
      RXN2      => rxn2,
      TXN1      => txn1,
      TXP1      => txp1,
      RXP1      => rxp1,
      RXN1      => rxn1,
      TXN0      => txn0,
      TXP0      => txp0,
      RXP0      => rxp0,
      RXN0      => rxn0
   );

-- ----------------------------------------------------
-- clk clock generator
lclkfgen : process
begin
   lclkf <= '1';
   wait for clkper/2;
   lclkf <= '0';
   wait for clkper/2;
end process;

-- -------------------------------------------------------------
-- clkf clock generator (125MHz)
clkfgen : process
begin
   clkf <= '1';
   wait for clkfper/2;
   clkf <= '0';
   wait for clkfper/2;
end process;

-- ----------------------------------------------------
-- PLX Simulation component
PLX_SIM_U : entity work.plx_sim
generic map(
   PLX_HOLD       => 10 ns,
   DEBUG_REPORT   => false
)
port map(
   -- PLX interface
   LCLKF       => lclkf,
   LAD(31 downto 27) => lad1,
   LAD(26 downto 0)  => lad0,
   LBE         => open,
   LHOLDA      => lholda,
   LFRAME      => open,
   ADS         => ads,
   BLAST       => blast,
   LWR         => lwr,
   READY       => ready,
   LHOLD       => lhold,
   LINT        => open,
   LRESET      => open,
   USERO       => open,

   -- Simulation interface
   STATUS      => plx_status,
   OPER        => plx_oper,
   PARAMS      => plx_params,
   STROBE      => plx_strobe,
   BUSY        => plx_busy
);

 lholda <= LHOLD after clkper;  -- FIXME

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
   wait for 0.1*clkper;
   plx_oper    <= ctrl.oper;
   plx_params  <= ctrl.params;
   plx_strobe  <= '1';

   wait for clkper;
   plx_strobe  <= '0';

   -- block waiting, if reguired
   if (block_wait) then
      wait until (LCLKF'event and LCLKF='1' and plx_busy = '0');
   end if;
end plx_op;

-- ----------------------------------------------------------------
--                        Testbench Body
-- ----------------------------------------------------------------
variable i : integer := 0;

begin

 -- local bus inicialization
 plx_op(plx_init,true);

 -- load transmit data
 plx_op(plx_write_file(LB_TEST_BASE_ADDR,data_file1));
 
 -- read transmit data
-- i := 0;
-- while (i < 50) loop
--   plx_op(plx_read(LB_TEST_BASE_ADDR + (i*4)));
--   i := i + 1;
-- end loop;

 -- start transmision
 plx_op(plx_write(LB_TEST_BASE_ADDR + 16#4000#,X"00000001"));

 wait for 1200 ns;

 -- read received data
-- i := 0;
-- while (i < 50) loop
--   plx_op(plx_read(LB_TEST_BASE_ADDR + 16#1000# + (i*4)));
--   i := i + 1;
-- end loop;
-- plx_op(plx_read(LB_TEST_BASE_ADDR + 16#1004#));
-- plx_op(plx_read(LB_TEST_BASE_ADDR + 16#1008#));
-- plx_op(plx_read(LB_TEST_BASE_ADDR + 16#100c#));

wait;


end process;

end architecture behavioral;
