-- ibuf_emac_empty.vhd: EMAC IBUF empty architecture
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

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture empty of ibuf_emac is

   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig : std_logic_vector(72+DATA_PATHS*8+log2(DATA_PATHS)-1 downto 0);

begin
   
   empty_sig <= RESET            & -- 1

                RXCLK            & -- 1
                RXCE             & -- 1
                RXD              & -- 8
                RXDV             & -- 1
                RXGOODFRAME      & -- 1
                RXBADFRAME       & -- 1
                RXSTATS          & -- 7
                RXSTATSVLD       & -- 1

                CTRL_DI          & -- DATA_PATHS * 8
                CTRL_REM         & -- log2(DATA_PATHS)
                CTRL_SRC_RDY_N   & -- 1
                CTRL_SOP_N       & -- 1
                CTRL_EOP_N       & -- 1
                CTRL_HDR_EN      & -- 1
                CTRL_FTR_EN      & -- 1
                CTRL_RDY         & -- 1

                SAU_ACCEPT       & -- 1
                SAU_DV           & -- 1

                RDCLK            & -- 1
                DST_RDY_N        & -- 1

                ADC_RD           & -- 1
                ADC_WR           & -- 1
                ADC_ADDR         & -- 6
                ADC_DI;            -- 32
                -- --------------------
                -- 72 + DATA_PATHS * 8 + log2(DATA_PATHS)
 
      CTRL_CLK                <= '0';
      CTRL_DST_RDY_N          <= '1';
      SOP                     <= '0';
      STAT.PAYLOAD_LEN        <= (others => '0');
      STAT.FRAME_ERROR        <= '1';
      STAT.MAC_CHECK_FAILED   <= '1';
      STAT.LEN_BELOW_MIN      <= '1';
      STAT.LEN_OVER_MTU       <= '0';
      STAT_DV                 <= '0';
      DATA                    <= (others => '0');
      DREM                    <= (others => '0');
      SRC_RDY_N               <= '1';
      SOF_N                   <= '1';
      SOP_N                   <= '1';
      EOF_N                   <= '1';
      EOP_N                   <= '1';
      ADC_CLK                 <= '0';
      ADC_DO                  <= (others => '0');
      ADC_DRDY                <= '0';

end architecture empty;
  
