--
-- ics_core.vhd: ICS core
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
entity ICS_CORE is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64;

      -- Internal Bus User Component 0
      IB_USER0_WR   : inout t_ibmi_write64;
      IB_USER0_RD   : inout t_ibmi_read64s;

      -- Internal Bus User Component 1
      IB_USER1_WR   : inout t_ibmi_write64;
      IB_USER1_RD   : inout t_ibmi_read64s;

      -- Internal Bus User Component 2
      IB_USER2_WR   : inout t_ibmi_write64;
      IB_USER2_RD   : inout t_ibmi_read64s;

      -- Internal Bus User Component 3 with BM
      IB_USER3_WR   : inout t_ibmi_write64;
      IB_USER3_RD   : inout t_ibmi_read64s;
      IB_USER3_BM   : inout t_ibbm_64;
      
      -- Local Bus User Component 0
      LB_USER0_CLK  : in std_logic;
      LB_USER0_MI32 : inout t_mi32;

      -- Local Bus User Component 1
      LB_USER1_CLK  : in std_logic;
      LB_USER1_MI32 : inout t_mi32;

      -- Local Bus User Component 2
      LB_USER2_CLK  : in std_logic;
      LB_USER2_MI32 : inout t_mi32;

      -- Local Bus User Component 3
      LB_USER3_CLK  : in std_logic;
      LB_USER3_MI32 : inout t_mi32;

      -- Local Bus User Component 4
      LB_USER4_CLK  : in std_logic;
      LB_USER4_MI32 : inout t_mi32;

      -- Local Bus User Component 5
      LB_USER5_CLK  : in std_logic;
      LB_USER5_MI32 : inout t_mi32;

      -- Local Bus User Component 6
      LB_USER6_CLK  : in std_logic;
      LB_USER6_MI32 : inout t_mi32
      );
end entity ICS_CORE;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ICS_CORE_ARCH of ICS_CORE is
 
     -- Internal Bus Switch 0 Signals
     signal ib_switch0_1     : t_internal_bus64;
     signal ib_switch0_2     : t_internal_bus64;
     -- Internal Bus Switch 1 Signals
     signal ib_switch1_1     : t_internal_bus64;
     signal ib_switch1_2     : t_internal_bus64;
     -- Internal Bus Switch 2 Signals
     signal ib_switch2_1     : t_internal_bus64;
     signal ib_switch2_2     : t_internal_bus64;
     -- Internal Bus Switch 3 Signals
     signal ib_switch3_1     : t_internal_bus64;
     signal ib_switch3_2     : t_internal_bus64;
     
     -- Local Bus 16 (LB_ROOT)
     signal local_bus16      : t_local_bus16;

     -- Local Bus Switch 0 Signals
     signal lb_switch0_1     : t_local_bus16;
     signal lb_switch0_2     : t_local_bus16;
     signal lb_switch0_3     : t_local_bus16;
     signal lb_switch0_4     : t_local_bus16;

     -- Local Bus Switch 1 Signals
     signal lb_switch1_1     : t_local_bus16;
     signal lb_switch1_2     : t_local_bus16;
     signal lb_switch1_3     : t_local_bus16;
     signal lb_switch1_4     : t_local_bus16;

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

-- -- Internal Bus Switch 1 ---------------------------------------------------
IB_SWITCH1_U : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => IB_SWITCH1_BASE,
      SWITCH_LIMIT       => IB_SWITCH1_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => IB_USER0_BASE,
      DOWNSTREAM0_LIMIT  => IB_USER0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => IB_SWITCH2_BASE, 
      DOWNSTREAM1_LIMIT  => IB_SWITCH2_LIMIT
   )

   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => ib_switch0_2,
      -- Downstream Ports
      PORT1          => ib_switch1_1,
      PORT2          => ib_switch1_2
   );

-- -- Internal Bus Switch 2 ---------------------------------------------------
IB_SWITCH2_U : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => IB_SWITCH2_BASE,
      SWITCH_LIMIT       => IB_SWITCH2_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => IB_USER1_BASE,
      DOWNSTREAM0_LIMIT  => IB_USER1_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => IB_SWITCH3_BASE, 
      DOWNSTREAM1_LIMIT  => IB_SWITCH3_LIMIT
   )

   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => ib_switch1_2,
      -- Downstream Ports
      PORT1          => ib_switch2_1,
      PORT2          => ib_switch2_2
   );

-- -- Internal Bus Switch 3 ---------------------------------------------------
IB_SWITCH3_U : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH         => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => IB_SWITCH3_BASE,
      SWITCH_LIMIT       => IB_SWITCH3_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => IB_USER2_BASE,
      DOWNSTREAM0_LIMIT  => IB_USER2_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => IB_USER3_BASE, 
      DOWNSTREAM1_LIMIT  => IB_USER3_LIMIT
   )

   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,
      -- Upstream Port
      PORT0          => ib_switch2_2,
      -- Downstream Ports
      PORT1          => ib_switch3_1,
      PORT2          => ib_switch3_2
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
      INTERNAL_BUS   => ib_switch1_1,
     
      -- User Component Interface
      WR             => IB_USER0_WR,
      RD             => IB_USER0_RD
   );

-- -- Internal Bus Endpoint Component 1 ---------------------------------------
IB_ENDPOINT1_U: entity work.IB_ENDPOINT
   generic map (
      LIMIT          => IB_USER1_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch2_1,
     
      -- User Component Interface
      WR             => IB_USER1_WR,
      RD             => IB_USER1_RD
   );

-- -- Internal Bus Endpoint Component 2 ---------------------------------------
IB_ENDPOINT2_U: entity work.IB_ENDPOINT
   generic map (
      LIMIT          => IB_USER2_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch3_1,
     
      -- User Component Interface
      WR             => IB_USER2_WR,
      RD             => IB_USER2_RD
   );

-- -- Internal Bus Endpoint Component 3 with BM -------------------------------
IB_ENDPOINT3_U: entity work.IB_ENDPOINT_MASTER
   generic map (
      LIMIT          => IB_USER3_LIMIT
   )
   port map (
      -- Common Interface
      IB_CLK         => CLK,
      IB_RESET       => RESET,

      -- Internal Bus Interface
      INTERNAL_BUS   => ib_switch3_2,
     
      -- User Component Interface
      WR             => IB_USER3_WR,
      RD             => IB_USER3_RD,

      -- Busmaster Interface
      BM             => IB_USER3_BM
   );

-- -- Local Bus 5-Port Switch 0 -----------------------------------------------
LB_SWITCH0_U : entity work.LB_SWITCH5
   port map (
      -- Common Interface
      LB_CLK         => CLK,
      LB_RESET       => RESET,

      -- Upstream Port
      PORT0          => local_bus16,
      -- Downstream Ports
      PORT1          => lb_switch0_1,
      PORT2          => lb_switch0_2,
      PORT3          => lb_switch0_3,
      PORT4          => lb_switch0_4
   );

-- -- Local Bus 5-Port Switch 1 -----------------------------------------------
LB_SWITCH1_U : entity work.LB_SWITCH5
   port map (
      -- Common Interface
      LB_CLK         => CLK,
      LB_RESET       => RESET,

      -- Upstream Port
      PORT0          => lb_switch0_4,
      -- Downstream Ports
      PORT1          => lb_switch1_1,
      PORT2          => lb_switch1_2,
      PORT3          => lb_switch1_3,
      PORT4          => lb_switch1_4
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
      LOCALBUS       => lb_switch0_1,

      -- User Component Interface
      CLK            => LB_USER0_CLK,
      MI32           => LB_USER0_MI32
  );

-- -- Local Bus Endpoint 1 ----------------------------------------------------   
LB_ENDPOINT1_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER1_BASE,
      LIMIT          => LB_USER1_LIMIT,
      FREQUENCY      => LB_USER1_FREQ,
      BUFFER_EN      => LB_USER1_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch0_2,

      -- User Component Interface
      CLK            => LB_USER1_CLK,
      MI32           => LB_USER1_MI32
  );

-- -- Local Bus Endpoint 2 ----------------------------------------------------   
LB_ENDPOINT2_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER2_BASE,
      LIMIT          => LB_USER2_LIMIT,
      FREQUENCY      => LB_USER2_FREQ,
      BUFFER_EN      => LB_USER2_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch0_3,

      -- User Component Interface
      CLK            => LB_USER2_CLK,
      MI32           => LB_USER2_MI32
  );

-- -- Local Bus Endpoint 3 ----------------------------------------------------   
LB_ENDPOINT3_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER3_BASE,
      LIMIT          => LB_USER3_LIMIT,
      FREQUENCY      => LB_USER3_FREQ,
      BUFFER_EN      => LB_USER3_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch1_1,

      -- User Component Interface
      CLK            => LB_USER3_CLK,
      MI32           => LB_USER3_MI32
  );

-- -- Local Bus Endpoint 4 ----------------------------------------------------   
LB_ENDPOINT4_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER4_BASE,
      LIMIT          => LB_USER4_LIMIT,
      FREQUENCY      => LB_USER4_FREQ,
      BUFFER_EN      => LB_USER4_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch1_2,

      -- User Component Interface
      CLK            => LB_USER4_CLK,
      MI32           => LB_USER4_MI32
  );

-- -- Local Bus Endpoint 5 ----------------------------------------------------   
LB_ENDPOINT5_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER5_BASE,
      LIMIT          => LB_USER5_LIMIT,
      FREQUENCY      => LB_USER5_FREQ,
      BUFFER_EN      => LB_USER5_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch1_3,

      -- User Component Interface
      CLK            => LB_USER5_CLK,
      MI32           => LB_USER5_MI32
  );

-- -- Local Bus Endpoint 6 ----------------------------------------------------   
LB_ENDPOINT6_U : entity work.LB_ENDPOINT
   generic map (
      BASE_ADDR      => LB_USER6_BASE,
      LIMIT          => LB_USER6_LIMIT,
      FREQUENCY      => LB_USER6_FREQ,
      BUFFER_EN      => LB_USER6_BUFFER
   )
   port map (
      -- Common Interface
      RESET          => RESET,

      -- Local Bus Interface
      LB_CLK         => CLK,
      LOCALBUS       => lb_switch1_4,

      -- User Component Interface
      CLK            => LB_USER6_CLK,
      MI32           => LB_USER6_MI32
  );

end architecture ICS_CORE_ARCH;

