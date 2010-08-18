-- mdio.vhd MDIO design architecture - MI32
-- Copyright (C) 2003-2009 CESNET
-- Author(s): Michal Janousek <xjanou11@stud.fit.vutbr.cz>
--            Stepan Friedl <friedl@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

architecture full of mdio_ctrl_mi32 is

   -- Registers
   signal reg_mdio_frame   : std_logic_vector(31 downto 0);
   signal reg_mdio_do      : std_logic_vector(15 downto 0);
   signal reg_mdio_busy    : std_logic;

   -- MDIO signals
   signal mdio_do    : std_logic_vector(15 downto 0);
   signal mdio_frame : std_logic_vector(31 downto 0);
   signal mdio_start : std_logic;
   signal mdio_busy  : std_logic;

begin

   MI_ARDY <= '1';
   mi_DRDY <= MI_RD;

   MDIO_CTRL  : entity work.mdio_c
   port map(
      CLK       => CLK,                  -- Input clock
      DIV_CLK   => "11110",              -- Divider ratio (for 125 MHz CLK)
      START_OP  => mdio_frame(1 downto 0),
      OPERATION => mdio_frame(3 downto 2),
      PHY_ADDR  => mdio_frame(8 downto 4),
      REG_ADDR  => mdio_frame(13 downto 9),
      DATA_IN   => mdio_frame(31 downto 16),
      DATA_OUT  => mdio_do,
      DATA_RDY  => open,
      RUN_OP    => mdio_start,
      BUSY      => mdio_busy,
      MDC       => MDC,                  -- MDIO Clock output
      MDIO_I    => MDIO_I,               -- MDIO Data - Input/Output
      MDIO_O    => MDIO_O,                -- MDIO Data - Input/Output
      MDIO_OE   => MDIO_OE               -- MDIO Data - Input/Output
   );

   -- WR decoder + registers
   MDIO_REGS : process(CLK,RESET)
   begin
      if (RESET = '1') then
         mdio_frame <= (others => '1');
         mdio_start <= '0';
      elsif (CLK'event AND CLK = '1') then
         mdio_start <= '0';
         -- Write to MDIO registers
         if (MI_WR = '1') then
            case MI_ADDR(3 downto 2) is
               -- 0x00 and 0x04
               when "00" | "01" => mdio_frame <= MI_DWR;
                                   mdio_start <= '1';
               when others => null;
            end case;
         end if;
      end if;
   end process;

   -- RD decoder
   rd_decoderp: process(MI_ADDR, reg_mdio_frame, reg_mdio_do, reg_mdio_busy)
   begin
      case MI_ADDR(3 downto 2) is
         -- 0x00
         when "00"   => MI_DRD <= reg_mdio_frame;
         -- 0x08
         when "10"   => MI_DRD <= X"0000" & reg_mdio_do;
         -- 0x0C
         when "11"   => MI_DRD <= X"0000000" & "000" & reg_mdio_busy;
         -- others
         when others => MI_DRD <= (others => '0');
      end case;
   end process;

   -- Register signals from the controler
   reg_mdio_framep: process(CLK, RESET)
   begin
      if (CLK'event AND CLK = '1') then
         reg_mdio_frame <= mdio_frame;
      end if;
   end process;

   reg_mdio_dop: process(CLK, RESET)
   begin
      if (RESET = '1') then
         reg_mdio_do <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         reg_mdio_do <= mdio_do;
      end if;
   end process;

   reg_mdio_busyp: process(CLK, RESET)
   begin
      if (CLK'event AND CLK = '1') then
         reg_mdio_busy <= mdio_busy;
      end if;
   end process;

end full;
-----------------------------------------------------------------
