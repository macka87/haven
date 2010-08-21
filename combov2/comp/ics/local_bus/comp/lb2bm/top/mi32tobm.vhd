--
-- mi32tobm.vhd: Easilly create busmaster transaction using mi32 interface
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MI32TOBM is
   port (
      -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;
      -- MI32 interface
      MI32           : inout t_mi32;
      -- Endpoint Busmaster interface
      BM             : inout t_ibbm_64
      );
end entity MI32TOBM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture MI32TOBM_ARCH of MI32TOBM is


begin


MI32TOBM_CORE_U : entity work.MI32TOBM_CORE
   port map (
      -- Common interface
      RESET          => RESET,
      CLK            => CLK,
      -- MI32 interface
      MI32           => MI32,
      -- Endpoint Busmaster interface
      GLOBAL_ADDR    => BM.GLOBAL_ADDR,
      LOCAL_ADDR     => BM.LOCAL_ADDR,
      LENGTH         => BM.LENGTH,
      TAG            => BM.TAG,
      TRANS_TYPE     => BM.TRANS_TYPE,
      REQ            => BM.REQ,
      -- Master Input interface
      ACK            => BM.ACK,
      OP_TAG         => BM.OP_TAG,
      OP_DONE        => BM.OP_DONE
      );


end architecture MI32TOBM_ARCH;
