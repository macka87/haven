--
-- ics_test_app.vhd: ICS Testing application
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
entity ICS_TEST_APP is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      INTERNAL_BUS  : inout t_internal_bus64
      );
end entity ICS_TEST_APP;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ICS_TEST_APP_ARCH of ICS_TEST_APP is
  
   -- Design identification --------------------------------------------
   constant ID_PROJECT      : std_logic_vector(15 downto 0):= X"0000";
   constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"01";
   constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"00";
   constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
   constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000";
   constant ID_PROJECT_TEXT : std_logic_vector(255 downto 0) :=
       X"4943532054657374204170706c69636174696f6e20312e300000000000000000";
   -- ------------------------------------------------------------------ 

      -- Internal Bus User Component 0
      signal ib_user0_wr   : t_ibmi_write64;
      signal ib_user0_rd   : t_ibmi_read64s;

      -- Internal Bus User Component 1
      signal ib_user1_wr   : t_ibmi_write64;
      signal ib_user1_rd   : t_ibmi_read64s;

      -- Internal Bus User Component 2
      signal ib_user2_wr   : t_ibmi_write64;
      signal ib_user2_rd   : t_ibmi_read64s;

      -- Internal Bus User Component 3 with BM
      signal ib_user3_wr   : t_ibmi_write64;
      signal ib_user3_rd   : t_ibmi_read64s;
      signal ib_user3_bm   : t_ibbm_64;
      
      -- Local Bus User Component 0
      signal lb_user0_mi32 : t_mi32;
      -- Local Bus User Component 1
      signal lb_user1_mi32 : t_mi32;
      -- Local Bus User Component 2
      signal lb_user2_mi32 : t_mi32;
      -- Local Bus User Component 3
      signal lb_user3_mi32 : t_mi32;
      -- Local Bus User Component 4
      signal lb_user4_mi32 : t_mi32;
      -- Local Bus User Component 5
      signal lb_user5_mi32 : t_mi32;
      -- Local Bus User Component 6
      signal lb_user6_mi32 : t_mi32;

      signal empty_sig     : std_logic_vector(31 downto 0);

begin
  

-- ----------------------------------------------------------------------------
ICS_CORE_U : entity work.ICS_CORE
   port map (
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Internal Bus Interface
      INTERNAL_BUS  => INTERNAL_BUS,

      -- Internal Bus User Component 0
      IB_USER0_WR   => ib_user0_wr,
      IB_USER0_RD   => ib_user0_rd,

      -- Internal Bus User Component 1
      IB_USER1_WR   => ib_user1_wr,
      IB_USER1_RD   => ib_user1_rd,

      -- Internal Bus User Component 2
      IB_USER2_WR   => ib_user2_wr,
      IB_USER2_RD   => ib_user2_rd,

      -- Internal Bus User Component 3 with BM
      IB_USER3_WR   => ib_user3_wr,
      IB_USER3_RD   => ib_user3_rd,
      IB_USER3_BM   => ib_user3_bm,
      
      -- Local Bus User Component 0
      LB_USER0_CLK  => CLK,
      LB_USER0_MI32 => lb_user0_mi32,

      -- Local Bus User Component 1
      LB_USER1_CLK  => CLK,
      LB_USER1_MI32 => lb_user1_mi32,

      -- Local Bus User Component 2
      LB_USER2_CLK  => CLK,
      LB_USER2_MI32 => lb_user2_mi32,

      -- Local Bus User Component 3
      LB_USER3_CLK  => CLK,
      LB_USER3_MI32 => lb_user3_mi32,

      -- Local Bus User Component 4
      LB_USER4_CLK  => CLK,
      LB_USER4_MI32 => lb_user4_mi32,

      -- Local Bus User Component 5
      LB_USER5_CLK  => CLK,
      LB_USER5_MI32 => lb_user5_mi32,

      -- Local Bus User Component 6
      LB_USER6_CLK  => CLK,
      LB_USER6_MI32 => lb_user6_mi32
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

-- -- Internal Bus User Component 1 -------------------------------------------
IBMI64MEM1_U : entity work.IBMI64MEM
   generic map (
      SIZE           => IB_USER1_MEM_SIZE,
      BRAM_DISTMEM   => IB_USER1_MEM_TYPE 
    )
   port map (
      -- Common Interface
      CLK            => CLK,
      RESET          => RESET,
      -- IBMI64 Interface
      IBMI_WRITE64   => ib_user1_wr, 
      IBMI_READ64    => ib_user1_rd 
   );

-- -- Internal Bus User Component 2 -------------------------------------------
IBMI64MEM2_U : entity work.IBMI64MEM
   generic map (
      SIZE           => IB_USER2_MEM_SIZE,
      BRAM_DISTMEM   => IB_USER2_MEM_TYPE 
    )
   port map (
      -- Common Interface
      CLK            => CLK,
      RESET          => RESET,
      -- IBMI64 Interface
      IBMI_WRITE64   => ib_user2_wr, 
      IBMI_READ64    => ib_user2_rd 
   );

-- -- Internal Bus User Component 3 -------------------------------------------
IBMI64MEM3_U : entity work.IBMI64MEM
   generic map (
      SIZE           => IB_USER3_MEM_SIZE,
      BRAM_DISTMEM   => IB_USER3_MEM_TYPE 
    )
   port map (
      -- Common Interface
      CLK            => CLK,
      RESET          => RESET,
      -- IBMI64 Interface
      IBMI_WRITE64   => ib_user3_wr, 
      IBMI_READ64    => ib_user3_rd 
   );


-- -- -- Local Bus User Component 0 ----------------------------------------------
-- MI32MEM0_U : entity work.MI32MEM
--    generic map (
--       SIZE         => LB_USER0_MEM_SIZE,
--       BRAM_DISTMEM => LB_USER0_MEM_TYPE
--     )
--    port map (
--       -- Common Interface
--       CLK          => CLK,
--       RESET        => RESET,
--       -- MI32 Interface
--       MI32         => lb_user0_mi32
--    );

-- -- Local Bus ID Component 0 ------------------------------------------------
   ID32_U: entity work.ID_COMP_MI32
   generic map(
      PROJECT_ID     => ID_PROJECT,
      SW_MAJOR       => ID_SW_MAJOR,
      SW_MINOR       => ID_SW_MINOR,
      HW_MAJOR       => ID_HW_MAJOR,
      HW_MINOR       => ID_HW_MINOR,
      PROJECT_TEXT   => ID_PROJECT_TEXT
   )
   port map(
      -- ID component interface
      CLK                  => CLK,
      RESET                => RESET,
      COMMAND              => empty_sig,
      MI                   => lb_user0_mi32,
      STATUS               => X"00000000000000000000000000000000",
      WE                   => "0000"
   );

-- -- Local Bus User Component 1 ----------------------------------------------
MI32MEM1_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER1_MEM_SIZE,
      BRAM_DISTMEM => LB_USER1_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user1_mi32
   );

-- -- Local Bus User Component 2 ----------------------------------------------
MI32MEM2_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER2_MEM_SIZE,
      BRAM_DISTMEM => LB_USER2_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user2_mi32
   );

-- -- Local Bus User Component 3 ----------------------------------------------
MI32MEM3_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER3_MEM_SIZE,
      BRAM_DISTMEM => LB_USER3_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user3_mi32
   );

-- -- Local Bus User Component 4 ----------------------------------------------
MI32MEM4_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER4_MEM_SIZE,
      BRAM_DISTMEM => LB_USER4_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user4_mi32
   );

-- -- Local Bus User Component 5 ----------------------------------------------
MI32MEM5_U : entity work.MI32MEM
   generic map (
      SIZE         => LB_USER5_MEM_SIZE,
      BRAM_DISTMEM => LB_USER5_MEM_TYPE
    )
   port map (
      -- Common Interface
      CLK          => CLK,
      RESET        => RESET,
      -- MI32 Interface
      MI32         => lb_user5_mi32
   );

-- ----------------------------------------------------------------------------
MI32TOBM_U: entity work.MI32TOBM
   port map (
      -- Common interface
      RESET          => RESET,
      CLK            => CLK,
      -- MI32 interface
      MI32           => lb_user6_mi32,
      -- Endpoint Busmaster interface
      BM             => ib_user3_bm
      );

end architecture ICS_TEST_APP_ARCH;

