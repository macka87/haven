-- rep_2port_sdr_top_arch.vhd: The architection that imlements rep_2port_sdr_top_ent
--     entity, that encapsulates rep_2port component (which contains repeater) 
--     and enable registers for enabling functionality of the repeater. 
--     These components are available through MI32 interface.                
--
-- Copyright (C) 2009 CESNET
-- Author(s):  Jiri Novotnak <xnovot87@stud.fit.vutbr.cz>
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
-- TODO: test & debug
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--  Architecture declaration: REP_2PORT_SDR_TOP_ARCH
-- ---------------------------------------------------------------------------- 
architecture rep_2port_sdr_top_arch of rep_2port_sdr_top is

   signal reg_en_0           : std_logic;
   signal reg_en_0_we        : std_logic;

   signal reg_en_1           : std_logic;
   signal reg_en_1_we        : std_logic;

begin

   REP_2PORT : entity work.xgmii_rep_2port
   generic map (
      FIFO_SIZE  => FIFO_SIZE
   )
   port map (
      RESET => RESET,

      -- Port 0 ---------------------------------------------------------------
      EN0        => reg_en_0,
      OVERFLOW0  => open,
      UNDERFLOW0 => open,

      RX_CLK0    => RX_CLK0,
      RX_D0      => RX_D0,
      RX_C0      => RX_C0,
      TX_CLK0    => TX_CLK0,
      TX_D0      => TX_D0,
      TX_C0      => TX_C0,

      -- Port 1 ---------------------------------------------------------------
      EN1        => reg_en_1,
      OVERFLOW1  => open,
      UNDERFLOW1 => open,

      RX_CLK1    => RX_CLK1,
      RX_D1      => RX_D1,
      RX_C1      => RX_C1,
      TX_CLK1    => TX_CLK1,
      TX_D1      => TX_D1,
      TX_C1      => TX_C1
   );

   -- Signal assigments
   IBUF0_CLK   <= RX_CLK0;
   IBUF0_DATA  <= RX_D0;
   IBUF0_CMD   <= RX_C0;

   IBUF1_CLK   <= RX_CLK1;
   IBUF1_DATA  <= RX_D1;
   IBUF1_CMD   <= RX_C1;


   MI32_ARDY   <= MI32_WR or MI32_RD;
   MI32_DRDY   <= MI32_RD;

   -- Input address decoder --------------------------------------------------
   mux_in : process(MI32_ADDR, MI32_WR, MI32_BE(0))
   begin
      reg_en_0_we <= '0';
      reg_en_1_we <= '0';

      case MI32_ADDR(4) is
         when '0' => 
            reg_en_0_we <= MI32_WR and MI32_BE(0); 
         when '1' =>
            reg_en_1_we <= MI32_WR and MI32_BE(0); 
         when others =>
            null;
      end case;
   end process;

   -- Output address decoder --------------------------------------------------
   mux_out: process(MI32_ADDR, reg_en_0, reg_en_1)
   begin
      MI32_DRD  <= (others => '0');

      case MI32_ADDR(4) is
         when '0' =>
            MI32_DRD(0) <= reg_en_0;
         when '1' =>
            MI32_DRD(0) <= reg_en_1;
         when others =>
            null;
      end case;
   end process;

   -- register reg_en_0 -------------------------------------------------------
   reg_en_0p: process(MI32_CLK)
   begin
      if (MI32_CLK'event AND MI32_CLK = '1') then
         if (RESET = '1') then
            reg_en_0 <= '1';
         elsif (reg_en_0_we = '1') then
            reg_en_0 <= MI32_DWR(0);
         end if;
      end if;
   end process;
   
   -- register reg_en_1 -------------------------------------------------------
   reg_en_1p: process(MI32_CLK)
   begin
      if (MI32_CLK'event AND MI32_CLK = '1') then
         if (RESET = '1') then
            reg_en_1 <= '1';
         elsif (reg_en_1_we = '1') then
            reg_en_1 <= MI32_DWR(0);
         end if;
      end if;
   end process;

end architecture rep_2port_sdr_top_arch;
