--
-- lb_endpoint_arch_full.vhd: Local Bus End Point Component
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky xkobie00@stud.fit.vutbr.cz
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

use work.lb_pkg.all; -- Internal Bus package
use work.math_pack.all; -- Math Pack
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_ENDPOINT_ARCH of LB_ENDPOINT is

   signal reset_pipe : std_logic;
   attribute equivalent_register_removal : string;
   attribute equivalent_register_removal of reset_pipe : signal is "no";

begin

assert (FREQUENCY = LOCAL_BUS_FREQUENCY) or (FREQUENCY = LOCAL_BUS_FREQUENCY/2)
report "lb_endpoint: Unsupported FREQUENCY" severity failure;

assert (to_integer(unsigned(BASE_ADDR)) rem to_integer(unsigned(LIMIT))) = 0
report "lb_endpoint BASE_ADDR must be N * LIMIT" severity failure;

-- ----------------------------------------------------------------------------
RESET_PIPE_P : process(RESET, LB_CLK)
   begin
      if LB_CLK'event and LB_CLK = '1' then
         reset_pipe  <= RESET;
      end if;
end process;

X50MHZ_U : if (FREQUENCY = (LOCAL_BUS_FREQUENCY/2)) generate

   LB_ENDPOINT_U : entity work.LB_ENDPOINT_50
   generic map(
      BASE_ADDR  => BASE_ADDR,
      LIMIT      => LIMIT,
      BUFFER_EN  => BUFFER_EN
   )
   port map(
      -- Common Interface
      RESET      => reset_pipe,
      
      -- Local Bus Interface
      LB_CLK      => LB_CLK,
      LB_DWR      => LOCALBUS.DWR,
      LB_BE       => LOCALBUS.BE,
      LB_ADS_N    => LOCALBUS.ADS_N,
      LB_RD_N     => LOCALBUS.RD_N,
      LB_WR_N     => LOCALBUS.WR_N,
      LB_DRD      => LOCALBUS.DRD,
      LB_RDY_N    => LOCALBUS.RDY_N,
      LB_ERR_N    => LOCALBUS.ERR_N,
      LB_ABORT_N  => LOCALBUS.ABORT_N,

      -- User Component Interface
      CLK         => CLK,
      MI32_DWR    => MI32.DWR,
      MI32_ADDR   => MI32.ADDR,
      MI32_RD     => MI32.RD,
      MI32_WR     => MI32.WR,
      MI32_BE     => MI32.BE,
      MI32_DRD    => MI32.DRD,
      MI32_ARDY   => MI32.ARDY,
      MI32_DRDY   => MI32.DRDY
   );
end generate;


X100MHZ_U: if (FREQUENCY = LOCAL_BUS_FREQUENCY) generate

   LB_ENDPOINT_U : entity work.LB_ENDPOINT_100
   generic map(
      BASE_ADDR  => BASE_ADDR,
      LIMIT      => LIMIT,
      BUFFER_EN  => BUFFER_EN
   )
   port map(
      -- Common Interface
      RESET      => reset_pipe,
      
      -- Local Bus Interface
      LB_CLK      => LB_CLK,
      LB_DWR      => LOCALBUS.DWR,
      LB_BE       => LOCALBUS.BE,
      LB_ADS_N    => LOCALBUS.ADS_N,
      LB_RD_N     => LOCALBUS.RD_N,
      LB_WR_N     => LOCALBUS.WR_N,
      LB_DRD      => LOCALBUS.DRD,
      LB_RDY_N    => LOCALBUS.RDY_N,
      LB_ERR_N    => LOCALBUS.ERR_N,
      LB_ABORT_N  => LOCALBUS.ABORT_N,

      -- User Component Interface
      CLK         => CLK,
      MI32_DWR    => MI32.DWR,
      MI32_ADDR   => MI32.ADDR,
      MI32_RD     => MI32.RD,
      MI32_WR     => MI32.WR,
      MI32_BE     => MI32.BE,
      MI32_DRD    => MI32.DRD,
      MI32_ARDY   => MI32.ARDY,
      MI32_DRDY   => MI32.DRDY
   );
end generate;


end architecture LB_ENDPOINT_ARCH;

