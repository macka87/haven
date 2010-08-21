--
-- ibuf_gmii_empty.vhd: Input buffer for gmii - empty architecture
--
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
-- TODO:
--
--

----------------------------------------------------------------------------
--                      Architecture declaration
----------------------------------------------------------------------------
architecture empty of ibuf_gmii is

   signal empty_sig : std_logic_vector((46 + ADDR_WIDTH - 1) downto 0);
   signal empty_pacodag : std_logic_vector((DATA_PATHS*8) + 2 + log2(DATA_PATHS) + 4);
   signal empty_sau  : std_logic_vector(1 downto 0);

begin
   empty_sig <= RESET    & --   1
                RXCLK    & --   1
                RXD      & --   8
                RXDV     & --   1
                RXER     & --   1
                RDCLK    & --   1
                DST_RDY_N  & --   1
                ADC_RD   & --   1
                ADC_WR   & --   1
                ADC_ADDR & --  ADDR_WIDTH
                ADC_DI;    --  32
                           -- ----
                           --  48 + ADDR_WIDTH
   empty_pacodag <= CTRL_DI      &
                    CTRL_DV      &
                    CTRL_HF      &
                    CTRL_REM     &
                    CTRL_EOP     &
                    CTRL_RDY;

   empty_sau <= SAU_ACCEPT    &
                SAU_DV;
   
   CTRL_CLK <= '0';
   SOP      <= '0';
   STAT     <= (others => '0');
   STAT_DV  <= '0';
   DATA     <= (others => '0');
   DREM     <= (others => '0');
   SRC_RDY_N<= '1';
   SOF_N    <= '1';
   SOP_N    <= '1';
   EOF_N    <= '1';
   EOP_N    <= '1';

   ADC_CLK  <= '0';
   ADC_DO   <= (others => '0');
   ADC_DRDY <= '0';

end architecture empty;

