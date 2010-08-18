--
-- ics_test_app_mini.vhd: ICS Testing application minimal
-- Copyright (C) 2007 CESNET
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.ib_pkg.all;
use work.lb_pkg.all;
use work.ics_test_app_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ICS_TEST_APP_MINI is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64
      );
end entity ICS_TEST_APP_MINI;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ICS_TEST_APP_MINI_ARCH of ICS_TEST_APP_MINI is
      
      -- Internal Bus User Component 0
      signal ib_user0_wr   : t_ibmi_write64;
      signal ib_user0_rd   : t_ibmi_read64s;
      
      -- Local Bus User Component 0
      signal lb_user0_mi32 : t_mi32;

begin
  

-- ----------------------------------------------------------------------------
ICS_CORE_U : entity work.ICS_CORE_MINI
   port map (
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Internal Bus Interface
      INTERNAL_BUS  => INTERNAL_BUS,

      -- Internal Bus User Component 0
      IB_USER0_WR   => ib_user0_wr,
      IB_USER0_RD   => ib_user0_rd,

      -- Local Bus User Component 0
      LB_USER0_CLK  => CLK,
      LB_USER0_MI32 => lb_user0_mi32
      );


-- -- Internal Bus User Component 0 -------------------------------------------
IBMI64MEM0_U : entity work.IBMI64MEM
   generic map (
      SIZE           => IB_USER0_MEM_SIZE,
      BRAM_DISTMEM   => IB_USER0_MEM_TYPE 
    )
   port map (
      -- Common Interface
      CLK            => CLK,
      RESET          => RESET,
      -- IBMI64 Interface
      IBMI_WRITE64   => ib_user0_wr, 
      IBMI_READ64    => ib_user0_rd 
   );

-- -- Local Bus User Component 0 ----------------------------------------------
MI32MEM0_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER0_MEM_SIZE,
      BRAM_DISTMEM => LB_USER0_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user0_mi32
   );


end architecture ICS_TEST_APP_MINI_ARCH;

