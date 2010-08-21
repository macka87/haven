--
-- lb_root.vhd: Local Bus Root Component
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus package
use work.lb_pkg.all; -- Local Bus package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LB_ROOT is
   generic(
      BASE_ADDR        : std_logic_vector(31 downto 0):=X"00000000";
      LIMIT            : std_logic_vector(31 downto 0):=X"00000100";

      -- Abort timeout counter width
      -- TIMEOUT and TIME will be 2**WIDTH cycles
      ABORT_CNT_WIDTH  : integer := 6
   );
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      RESET         : in std_logic;

      -- Local Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;

      -- Local Bus Interface
      LOCAL_BUS     : inout t_local_bus16
  );
end entity LB_ROOT;
