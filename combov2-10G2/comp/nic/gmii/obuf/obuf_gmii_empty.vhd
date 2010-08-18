--
-- obuf_gmii_empty.vhd: Output buffer for gmii - empty architecture
--
-- Copyright (C) 2004 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
architecture empty of obuf_gmii is

   signal empty_sig : std_logic_vector((44 + DATA_PATHS*9 + 7 - 1) downto 0);

begin
   empty_sig <= RESET    & --   1
                WRCLK    & --   1
                DI       & --  DATA_PATHS*8
                DI_CMD   & --  DATA_PATHS
                REFCLK   & --   1
                ADC_RD   & --   1
                ADC_WR   & --   1
                ADC_ADDR & --  ADDR_WIDTH = 7
                ADC_DI;    --  32
                           -- ----
                           --  44 + DATA_PATHS*9 + ADDR_WIDTH

   TXCLK    <= '0';
   TXD      <= (others => '0');
   TXEN	    <= '0';
   TXER     <= '0';
   FULL     <= '0';

   ADC_CLK  <= '0';
   ADC_DO   <= (others => '0');
   ADC_DRDY <= '0';

end architecture empty;

