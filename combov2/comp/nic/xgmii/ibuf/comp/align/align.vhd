-- align.vhd: Aligns the SDR XGMII protocol
-- Copyright (C) 2007 CESNET
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_pkg.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture ALIGN_ARCH of ALIGN is
   -- Constants declaration
   constant CONST_SOP_ALIGNED    : std_logic_vector(1 downto 0) := "01";
   constant CONST_SOP_INACTIVE   : std_logic_vector(1 downto 0) := "00";

   -- Signals declaration
   -- input
   signal rxd_in                 : std_logic_vector(63 downto 0);
   signal rxc_in                 : std_logic_vector(7 downto 0);

   -- SOP aligned pipeline
   signal mask_sop               : std_logic_vector(1 downto 0);
   signal sop_active1            : std_logic_vector(1 downto 0);
   signal sop_aligned2           : std_logic;
   signal sop_active2            : std_logic;
   signal reg2_sop_aligned       : std_logic;
   signal reg2_sop_aligned_we    : std_logic;

   -- Data pipeline
   signal reg2_rxd               : std_logic_vector(63 downto 0);
   signal mx_data_align_in_0     : std_logic_vector(63 downto 0);
   signal mx_data_align_in_1     : std_logic_vector(63 downto 0);
   signal mx_data_align          : std_logic_vector(63 downto 0);
   signal reg_rxd_align          : std_logic_vector(63 downto 0);

   -- Control data pipeline
   signal reg2_rxc               : std_logic_vector(7 downto 0);
   signal mx_cmd_align_in_0      : std_logic_vector(7 downto 0);
   signal mx_cmd_align_in_1      : std_logic_vector(7 downto 0);
   signal mx_cmd_align           : std_logic_vector(7 downto 0);
   signal reg_rxc_align          : std_logic_vector(7 downto 0);

   -- SOP pipeline
   signal reg2_sop_align         : std_logic;
   signal reg_sop_align          : std_logic;

begin

   -- input signals
   rxd_in <= RXD;
   rxc_in <= RXC;

   -- reg2_sop_aligned input logic
   mask_sop0p: process(rxd_in(7 downto 0))
   begin
      if (rxd_in(7 downto 0) = C_XGMII_SOP) then
         mask_sop(0) <= '1';
      else
         mask_sop(0) <= '0';
      end if;
   end process;
   mask_sop1p: process(rxd_in(39 downto 32))
   begin
      if (rxd_in(39 downto 32) = C_XGMII_SOP) then
         mask_sop(1) <= '1';
      else
         mask_sop(1) <= '0';
      end if;
   end process;

   sop_active1 <= mask_sop and (rxc_in(4) & rxc_in(0));
   
   sop_aligned2p: process(sop_active1)
   begin
      if (sop_active1 = CONST_SOP_ALIGNED) then
         sop_aligned2 <= '1';
      else
         sop_aligned2 <= '0';
      end if;
   end process;

   sop_active2p: process(sop_active1)
   begin
      if (sop_active1 /= CONST_SOP_INACTIVE) then
         sop_active2 <= '1';
      else
         sop_active2 <= '0';
      end if;
   end process;

   -- register reg2_sop_aligned
   reg2_sop_aligned_we <= sop_active2;
   reg2_sop_alignedp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg2_sop_aligned <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg2_sop_aligned_we = '1') then
            reg2_sop_aligned <= sop_aligned2;
         end if;
      end if;
   end process;



   -- register reg2_rxd
   reg2_rxdp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_rxd <= rxd_in;
      end if;
   end process;

   -- mx_data_align input signals
   mx_data_align_in_0 <= rxd_in(31 downto 0) & reg2_rxd(63 downto 32);
   mx_data_align_in_1 <= reg2_rxd;

   -- multiplexor mx_data_align
   mx_data_alignp: process(
                   reg2_sop_aligned, mx_data_align_in_0, mx_data_align_in_1)
   begin
      case reg2_sop_aligned is
         when '0' => mx_data_align <= mx_data_align_in_0;
         when '1' => mx_data_align <= mx_data_align_in_1;
         when others => mx_data_align <= (others => 'X');
      end case;
   end process;

   -- register reg_rxd_align
   reg_rxd_alignp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_rxd_align <= mx_data_align;
      end if;
   end process;



   -- register reg2_rxc
   reg2_rxcp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg2_rxc <= rxc_in;
      end if;
   end process;

   -- mx_cmd_align input signals
   mx_cmd_align_in_0 <= rxc_in(3 downto 0) & reg2_rxc(7 downto 4);
   mx_cmd_align_in_1 <= reg2_rxc;

   -- multiplexor mx_cmd_align
   mx_cmd_alignp: process(
                   reg2_sop_aligned, mx_cmd_align_in_0, mx_cmd_align_in_1)
   begin
      case reg2_sop_aligned is
         when '0' => mx_cmd_align <= mx_cmd_align_in_0;
         when '1' => mx_cmd_align <= mx_cmd_align_in_1;
         when others => mx_cmd_align <= (others => 'X');
      end case;
   end process;

   -- register reg_rxc_align
   reg_rxc_alignp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_rxc_align <= mx_cmd_align;
      end if;
   end process;

   

   -- register reg2_sop_align
   reg2_sop_alignp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg2_sop_align <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg2_sop_align <= sop_active2;
      end if;
   end process;

   -- register reg_sop_align
   reg_sop_alignp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_sop_align <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_sop_align <= reg2_sop_align;
      end if;
   end process;



   -- output signals
   RXD_ALIGNED <= reg_rxd_align;
   RXC_ALIGNED <= reg_rxc_align;
   SOP_ALIGNED <= reg_sop_align;

end architecture ALIGN_ARCH;
