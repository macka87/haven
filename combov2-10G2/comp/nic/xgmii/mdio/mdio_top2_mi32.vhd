-- mdio_top2_mi32.vhd MDIO top level wrapper
-- Copyright (C) 2003-2009 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

-- -------------------------------------------------------
--                 Entity declaration
-- -------------------------------------------------------
entity mdio_ctrl_top2_mi32 is

   port (
      -- Common interface
      RESET    : in    std_logic;
      CLK      : in    std_logic; -- 50MHz or 100MHz

      -- Mdio interface
      MDCA     : out std_logic; -- MDIO A Clock output
      MDIOA_I  : in  std_logic; -- MDIO A Input data
      MDIOA_O  : out std_logic; -- MDIO A Output data
      MDIOA_OE : out std_logic; -- MDIO A Output Enable, active low
      MDCB     : out std_logic; -- MDIO B Clock output
      MDIOB_I  : in  std_logic; -- MDIO B Input data
      MDIOB_O  : out std_logic; -- MDIO B Output data
      MDIOB_OE : out std_logic; -- MDIO B Output Enable, active low

      -- MI32 interface
      -- Input Data
      MI_DWR            : in  std_logic_vector(31 downto 0);
      -- Address
      MI_ADDR           : in  std_logic_vector(31 downto 0);
      -- Read Request
      MI_RD             : in  std_logic;
      -- Write Request
      MI_WR             : in  std_logic;
      -- Byte Enable
      MI_BE             : in  std_logic_vector(3  downto 0);
      -- Output Data
      MI_DRD            : out std_logic_vector(31 downto 0);
      -- Address Ready
      MI_ARDY           : out std_logic;
      -- Data Ready
      MI_DRDY           : out std_logic

   );
end mdio_ctrl_top2_mi32;

architecture full of mdio_ctrl_top2_mi32 is

   signal mdio_sel         : std_logic;
   signal mdioa_sel        : std_logic;
   signal mdiob_sel        : std_logic;

   signal mdioa_rd         : std_logic;
   signal mdioa_wr         : std_logic;
   signal mdioa_drd        : std_logic_vector(31 downto 0);
   signal mdioa_drdy       : std_logic;
   signal mdioa_ardy       : std_logic;

   signal mdiob_rd         : std_logic;
   signal mdiob_wr         : std_logic;
   signal mdiob_drd        : std_logic_vector(31 downto 0);
   signal mdiob_drdy       : std_logic;
   signal mdiob_ardy       : std_logic;

   signal mi_addr_local    : std_logic_vector(31 downto 0);

begin

   -- Read/write logic
   -- 0x20 is the mask for controler determining bit
   mdio_sel <= MI_ADDR(5);
   mdioa_sel <= not mdio_sel;
   mdiob_sel <= mdio_sel;

   mdioa_rd <= mdioa_sel and MI_RD;
   mdioa_wr <= mdioa_sel and MI_WR;

   mdiob_rd <= mdiob_sel and MI_RD;
   mdiob_wr <= mdiob_sel and MI_WR;

   -- Remove upper part of the MI32 address
   mi_addr_local(31 downto 5) <= (others => '0');
   mi_addr_local(4 downto 0)  <= MI_ADDR(4 downto 0);

   -- Controlers
   MDIO_CTRL_MI32_Ia : entity work.MDIO_CTRL_MI32
      port map (
         -- Common interface
         RESET    => RESET,
         CLK      => CLK,

         -- Mdio interface
         MDC      => MDCA,
         MDIO_I   => MDIOA_I,
         MDIO_O   => MDIOA_O,
         MDIO_OE  => MDIOA_OE,

         -- MI32 interface
         MI_DWR   => MI_DWR,
         MI_ADDR  => mi_addr_local,
         MI_RD    => mdioa_rd,
         MI_WR    => mdioa_wr,
         MI_BE    => MI_BE,
         MI_DRD   => mdioa_drd,
         MI_ARDY  => mdioa_ardy,
         MI_DRDY  => mdioa_drdy
      );

   MDIO_CTRL_MI32_Ib : entity work.MDIO_CTRL_MI32
      port map (
         -- Common interface
         RESET    => RESET,
         CLK      => CLK,

         -- Mdio interface
         MDC      => MDCB,
         MDIO_I   => MDIOB_I,
         MDIO_O   => MDIOB_O,
         MDIO_OE  => MDIOB_OE,

         -- MI32 interface
         MI_DWR   => MI_DWR,
         MI_ADDR  => mi_addr_local,
         MI_RD    => mdiob_rd,
         MI_WR    => mdiob_wr,
         MI_BE    => MI_BE,
         MI_DRD   => mdiob_drd,
         MI_ARDY  => mdiob_ardy,
         MI_DRDY  => mdiob_drdy
      );

   -- Output multiplexers
   process(mdio_sel, mdioa_drd, mdioa_drdy, mdioa_ardy, mdiob_drd, mdiob_drdy, mdiob_ardy)
   begin
      if (mdio_sel = '0') then
         MI_DRD  <= mdioa_drd;
         MI_DRDY <= mdioa_drdy;
         MI_ARDY <= mdioa_ardy;
      else
         MI_DRD  <= mdiob_drd;
         MI_DRDY <= mdiob_drdy;
         MI_ARDY <= mdiob_ardy;
      end if;
   end process;

end architecture;
