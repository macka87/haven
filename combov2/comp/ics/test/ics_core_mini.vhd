--
-- ics_core_mini.vhd: ICS core minimal solution
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
use work.ics_core_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ICS_CORE_MINI is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;

      -- Internal Bus User Component 0
      IB_USER0_WR   : inout t_ibmi_write64;
      IB_USER0_RD   : inout t_ibmi_read64s;
      
      -- Local Bus User Component 0
      LB_USER0_CLK  : in std_logic;
      LB_USER0_MI32 : inout t_mi32
      );
end entity ICS_CORE_MINI;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ICS_CORE_MINI_ARCH of ICS_CORE_MINI is
 
     -- Internal Bus Switch 0 Signals
     signal ib_switch0_1     : t_internal_bus64;
     signal ib_switch0_2     : t_internal_bus64;
  
     -- Local Bus 16 (LB_ROOT)
     signal local_bus16      : t_local_bus16;

begin

-- -- Internal Bus Switch 0 ---------------------------------------------------
IB_SWITCH0_U : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => IB_SWITCH0_BASE,
      SWITCH_LIMIT       => IB_SWITCH0_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => LOCALBUS_BASE,
      DOWNSTREAM0_LIMIT  => LOCALBUS_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => IB_SWITCH1_BASE, 
      DOWNSTREAM1_LIMIT  => IB_SWITCH1_LIMIT
   )

   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => INTERNAL_BUS,
      -- Downstream Ports
      PORT1          => ib_switch0_1,
      PORT2          => ib_switch0_2
   );

-- -- Internal Bus to Local Bus Bridge ----------------------------------------
LB_ROOT_U : entity work.LB_ROOT
   generic map (
      BASE_ADDR      => LOCALBUS_BASE,
      LIMIT          => LOCALBUS_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      RESET          => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch0_1,

      -- Local Bus Interface
      LOCAL_BUS      => local_bus16
  );


-- -- Internal Bus Endpoint Component 0 ---------------------------------------
IB_ENDPOINT0_U: entity work.IB_ENDPOINT
   generic map (
      LIMIT          => IB_USER0_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch0_2,
     
      -- User Component Interface
      WR             => IB_USER0_WR,
      RD             => IB_USER0_RD
   );


-- -- Local Bus Endpoint 0 ----------------------------------------------------   
LB_ENDPOINT0_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER0_BASE,
      LIMIT          => LB_USER0_LIMIT,
      FREQUENCY      => LB_USER0_FREQ,
      BUFFER_EN      => LB_USER0_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => local_bus16,

      -- User Component Interface
      CLK            => LB_USER0_CLK,
      MI32           => LB_USER0_MI32
  );
end architecture ICS_CORE_MINI_ARCH;

