--
-- ibuf_gmii_top4_hfe2_empty.vhd: 4 ibufs top level - empty architecture
-- Copyright (C) 2003 CESNET
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
architecture empty of ibuf_gmii_top4_hfe2 is

signal empty_sig : std_logic_vector(2 + 4*12 + 25 - 1 downto 0);
begin
   empty_sig <= RESET         &  -- 1
                RDCLK         &  -- 1

                IBUF0_RD      &  -- 1
                IBUF0_RXCLK   &  -- 1
                IBUF0_RXD     &  -- 8
                IBUF0_RXDV    &  -- 1
                IBUF0_RXER    &  -- 1

                IBUF1_RD      &  -- 1
                IBUF1_RXCLK   &  -- 1
                IBUF1_RXD     &  -- 8
                IBUF1_RXDV    &  -- 1
                IBUF1_RXER    &  -- 1

                IBUF2_RD      &  -- 1
                IBUF2_RXCLK   &  -- 1
                IBUF2_RXD     &  -- 8
                IBUF2_RXDV    &  -- 1
                IBUF2_RXER    &  -- 1

                IBUF3_RD      &  -- 1
                IBUF3_RXCLK   &  -- 1
                IBUF3_RXD     &  -- 8
                IBUF3_RXDV    &  -- 1
                IBUF3_RXER    &  -- 1

                LBCLK         &  -- 1
		LBFRAME       &  -- 1
                LBAS          &  -- 5
                LBRW          &  -- 1
                LBLAST        &  -- 1
                LBAD;            -- 16
      

   IBUF0_DO       <= (others => '0');
   IBUF0_DO_CMD   <= (others => '0');
   IBUF0_DO_DV    <= '0';

   IBUF1_DO       <= (others => '0');
   IBUF1_DO_CMD   <= (others => '0');
   IBUF1_DO_DV    <= '0';

   IBUF2_DO       <= (others => '0');
   IBUF2_DO_CMD   <= (others => '0');
   IBUF2_DO_DV    <= '0';

   IBUF3_DO       <= (others => '0');
   IBUF3_DO_CMD   <= (others => '0');
   IBUF3_DO_DV    <= '0';

   LBHOLDA	 <= 'Z';
   LBRDY	 <= 'Z';
   LBAD		 <= (others => 'Z');

end architecture empty;

