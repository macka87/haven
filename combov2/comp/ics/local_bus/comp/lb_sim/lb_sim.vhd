-- lb_sim.vhd: Simulation component for LocalBus interface
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use work.ib_pkg.all;      -- Internal Bus Package
use work.lb_pkg.all;      -- Local Bus Package
use work.ib_sim_oper.all; -- in_sim Package
use work.math_pack.all; -- Math Pack

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_SIM is
   generic(
      UPSTREAM_LOG_FILE   : string := "";
      DOWNSTREAM_LOG_FILE : string := "";
      BASE_ADDR           : std_logic_vector(31 downto 0):= X"00000000";
      LIMIT               : std_logic_vector(31 downto 0):= X"01048576"
   );
   port(
      -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- User Component Interface
      DWR        : out std_logic_vector(15 downto 0);
      BE         : out std_logic_vector(1 downto 0);
      ADS_N      : out std_logic;
      RD_N       : out std_logic;
      WR_N       : out std_logic;
      DRD        : in  std_logic_vector(15 downto 0);
      RDY_N      : in  std_logic;
      ERR_N      : in  std_logic;
      ABORT_N    : out std_logic;

      -- IB SIM interface
      STATUS            : out t_ib_status;
      CTRL              : in  t_ib_ctrl;
      STROBE            : in  std_logic;
      BUSY              : out std_logic
  );
end entity LB_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture LB_SIM_ARCH of LB_SIM is

     -- Internal Bus 64 (IB_SIM)
     signal internal_bus64      : t_internal_bus64;
     
     -- Local Bus 16 (LB_ROOT)
     signal local_bus16         : t_local_bus16;

begin

-- Internal Bus simulation component -----------------------------------------   
IB_SIM_U : entity work.IB_SIM
   generic map (
      UPSTREAM_LOG_FILE   => UPSTREAM_LOG_FILE,
      DOWNSTREAM_LOG_FILE => DOWNSTREAM_LOG_FILE
   )
   port map (
      -- Common interface
      IB_RESET           => RESET,
      IB_CLK             => CLK,

      -- Internal Bus Interface
      INTERNAL_BUS       => internal_bus64,

      -- IB SIM interface
      STATUS             => STATUS,
      CTRL               => CTRL,
      STROBE             => STROBE,
      BUSY               => BUSY
      );

-- -----------------------Portmaping of LB root -------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => BASE_ADDR,
      LIMIT          => LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      RESET          => RESET,

      -- Local Bus Interface
      INTERNAL_BUS   => internal_bus64,

      -- Local Bus Interface
      LOCAL_BUS      => local_bus16
   );


   DWR        <= local_bus16.dwr;
   BE         <= local_bus16.be;
   ADS_N      <= local_bus16.ads_n;
   RD_N       <= local_bus16.rd_n;
   WR_N       <= local_bus16.wr_n;
   ABORT_N    <= local_bus16.abort_n;
   local_bus16.drd   <= DRD;
   local_bus16.rdy_n <= RDY_N;
   local_bus16.err_n <= ERR_N;

end architecture  LB_SIM_ARCH;
