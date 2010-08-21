--
-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2003 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
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

   signal lclkf    : std_logic;
   signal lad      : std_logic_vector(31 downto 0);
   signal lbe      : std_logic_vector(3 downto 0);
   signal dp       : std_logic_vector(3 downto 0);
   signal den      : std_logic;
   signal dtr      : std_logic;
   signal ccs      : std_logic;
   signal lholda   : std_logic;
   signal breqi    : std_logic;
   signal lframe   : std_logic;
   signal ads      : std_logic;
   signal blast    : std_logic;
   signal lwr      : std_logic;
   signal ready    : std_logic;
   signal waitio   : std_logic;
   signal lhold    : std_logic;
   signal lint     : std_logic;
   signal lreset   : std_logic;
   signal useri    : std_logic;
   signal lserr    : std_logic;
   signal eot      : std_logic;
   signal bigend   : std_logic;
   signal usero    : std_logic;
   signal bterm    : std_logic;
   signal breqo    : std_logic;
   signal l_onoff  : std_logic;

   -- plx simulation signals
   signal plx_ctrl            : t_plx_ctrl;
   signal plx_oper            : t_plx_oper := INIT;
   signal plx_params          : t_plx_params;
   signal plx_strobe          : std_logic := '0';
   signal plx_busy            : std_logic;

   constant clkper      : time := 20 ns;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.fpga
port map(
   -- FPGA
   LCLKF    => lclkf,

   -- PLX interface
   LAD      => lad,
   LBE      => lbe,
   DP       => dp,
   DEN      => den,
   DTR      => dtr,
   CCS      => ccs,
   LHOLDA   => lholda,
   BREQI    => breqi,
   LFRAME   => lframe,
   ADS      => ads,
   BLAST    => blast,
   LWR      => lwr,
   READY    => ready,
   WAITIO   => waitio,
   LHOLD    => lhold,
   LINT     => lint,
   LRESET   => lreset,
   USERI    => useri,
   LSERR    => lserr,
   EOT      => eot,
   BIGEND   => bigend,
   USERO    => usero,
   BTERM    => bterm,
   BREQO    => breqo,
   L_ONOFF  => l_onoff
);

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
   LRESET      => lreset,
   USERO       => usero,

   -- Simulation interface
   OPER        => plx_oper,
   PARAMS      => plx_params,
   STROBE      => plx_strobe,
   BUSY        => plx_busy
);

-- ----------------------------------------------------
-- LCLKF clock generator
clkgen : process
begin
   lclkf <= '1';
   wait for clkper/2;
   lclkf <= '0';
   wait for clkper/2;
end process;

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
begin

   -- local bus inicialization
   plx_op(plx_init, true);

   -- Read results
   plx_op(plx_read(10#0#),true);

   plx_op(plx_read(10#4#),true);

   plx_op(plx_read(10#8#),true);

   plx_op(plx_read(10#12#),true);

   plx_op(plx_read(10#16#),true);

   plx_op(plx_read(10#20#),true);

   wait;
end process;

-- ----------------------------------------------------------------
end architecture behavioral;

