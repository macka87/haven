-- phyter_i2c_norec.vhd: Phyter control & status component (no MI32 record)
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.all;
-- pragma translate_on

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full of PHYTER_I2C_GENERIC_NOREC is

   type t_phy    is array(IFC_CNT downto 0)   of std_logic_vector(7 downto 0);
   type t_phy_wr is array(IFC_CNT-1 downto 0) of std_logic_vector(5 downto 0);
   type t_phy_rd is array(IFC_CNT-1 downto 0) of std_logic_vector(1 downto 0);

   signal phy        : t_phy;
   signal phy_wr     : t_phy_wr;
   signal phy_rd     : t_phy_rd;
   signal phy_wr_en  : std_logic_vector(IFC_CNT-1 downto 0);

   signal phy_addr3  : integer := 0;
   signal phy_addr2  : integer := 0;
   signal phy_addr1  : integer := 0;
   signal phy_addr0  : integer := 0;

   -- ---------------------------------------------------------------------

begin

   MI32_ARDY   <= MI32_RD or MI32_WR;
   MI32_DRDY   <= MI32_RD;
   MI32_DRD    <= phy(phy_addr3) &
                  phy(phy_addr2) &
                  phy(phy_addr1) &
                  phy(phy_addr0);

   -- enable phyters
   PHDIS <= (others => '0');

   GEN_PHY: for i in IFC_CNT-1 downto 0 generate
      phy(i) <= phy_wr(i) & phy_rd(i);
   end generate;
   -- dummy signal
   phy(IFC_CNT) <= (others => '0');

   sw_addr_decp: process(MI32_WR, phy_addr3, phy_addr2, phy_addr1, phy_addr0)
   begin
      phy_wr_en <= (others => '0');
      if (MI32_WR = '1') then
         phy_wr_en(phy_addr3)  <= '1';
         phy_wr_en(phy_addr2)  <= '1';
         phy_wr_en(phy_addr1)  <= '1';
         phy_wr_en(phy_addr0)  <= '1';
      end if;
   end process;

   phy_addrp: process(MI32_ADDR(4 downto 0))
   begin
      if (3+conv_integer(MI32_ADDR(4 downto 0)) < IFC_CNT) then
         phy_addr3 <= 3+conv_integer(MI32_ADDR(4 downto 0));
      else
         phy_addr3 <= IFC_CNT;
      end if;
      if (2+conv_integer(MI32_ADDR(4 downto 0)) < IFC_CNT) then
         phy_addr2 <= 2+conv_integer(MI32_ADDR(4 downto 0));
      else
         phy_addr2 <= IFC_CNT;
      end if;
      if (1+conv_integer(MI32_ADDR(4 downto 0)) < IFC_CNT) then
         phy_addr1 <= 1+conv_integer(MI32_ADDR(4 downto 0));
      else
         phy_addr1 <= IFC_CNT;
      end if;
      if (0+conv_integer(MI32_ADDR(4 downto 0)) < IFC_CNT) then
         phy_addr0 <= 0+conv_integer(MI32_ADDR(4 downto 0));
      else
         phy_addr0 <= IFC_CNT;
      end if;
   end process;

   -- ---------------------------------------------------------------------
   --                   Registers
   -- ---------------------------------------------------------------------
   GEN_PHY_WR: for i in IFC_CNT-1 downto 0 generate
      phy_wrp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            phy_wr(i) <= (others => '0');
         elsif (CLK'event AND CLK = '1') then
            if (MI32_WR = '1') then
               if (MI32_BE(i mod 4) = '1' and phy_wr_en(i) = '1') then
                  phy_wr(i) <= MI32_DWR(((7+i*8) mod 32) downto ((2+i*8) mod 32));
               end if;
            end if;
         end if;
      end process;
   end generate;

   -- ---------------------------------------------------------------------
   --                   Components
   -- ---------------------------------------------------------------------
   GEN_I2C_SW: for i in IFC_CNT-1 downto 0 generate
      I2C_SW_I: entity work.I2C_SW
         port map(
            CLK         => CLK,
            RESET       => RESET,
            --
            WR_DATA     => phy_wr(i)(4),
            WR_DATA_Z   => phy_wr(i)(3),
            WR_CLK      => phy_wr(i)(2),
            WR_CLK_Z    => phy_wr(i)(1),
            WRITE       => phy_wr(i)(0),
            --
            RD_DATA     => phy_rd(i)(1),
            RD_CLK      => phy_rd(i)(0),
            --
            I2C_CLK     => SCL(i),
            I2C_DATA    => SDA(i)
         );
   end generate;

end architecture full;
