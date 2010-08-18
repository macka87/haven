--
-- obuf_gmii_top4_empty.vhd: 4 obufs top level - empty architecture
-- Copyright (C) 2003 CESNET
-- Author(s): Tobola Jiri  tobola@liberouter.org
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
architecture empty of obuf_gmii_top4 is

signal empty_sig : std_logic_vector(3 + ((DATA_PATHS*8)+(log2(DATA_PATHS))+5)*4 + 21 - 1 downto 0);
begin
   empty_sig <= RESET            &
                WRCLK            & 	-- 3
		          REFCLK		      &

               OBUF0_DATA        &
               OBUF0_DREM        &
               OBUF0_SRC_RDY_N   &
               OBUF0_SOF_N       &
               OBUF0_SOP_N       &
               OBUF0_EOF_N       &
               OBUF0_EOP_N       &

               OBUF1_DATA        &
               OBUF1_DREM        &
               OBUF1_SRC_RDY_N   &
               OBUF1_SOF_N       &
               OBUF1_SOP_N       &
               OBUF1_EOF_N       &
               OBUF1_EOP_N       &

               OBUF2_DATA        &
               OBUF2_DREM        &
               OBUF2_SRC_RDY_N   &
               OBUF2_SOF_N       &
               OBUF2_SOP_N       &
               OBUF2_EOF_N       &
               OBUF2_EOP_N       &

               OBUF3_DATA        &
               OBUF3_DREM        &
               OBUF3_SRC_RDY_N   &
               OBUF3_SOF_N       &
               OBUF3_SOP_N       &
               OBUF3_EOF_N       &
               OBUF3_EOP_N       &

               LBCLK		         &
		         LBFRAME		      &
               LBAS              &   	-- 5
               LBRW              &
               LBLAST            &
               LBAD; 			         --16
      

   OBUF0_TXCLK       <= '0';
   OBUF0_TXD         <= (others => '0');
   OBUF0_TXEN        <= '0';
   OBUF0_TXER        <= '0';
   OBUF0_DST_RDY_N   <= '0';
                
   OBUF1_TXCLK       <= '0';
   OBUF1_TXD         <= (others => '0');
   OBUF1_TXEN        <= '0';
   OBUF1_TXER        <= '0';
   OBUF1_DST_RDY_N   <= '0';
                
   OBUF2_TXCLK       <= '0';
   OBUF2_TXD         <= (others => '0');
   OBUF2_TXEN        <= '0';
   OBUF2_TXER        <= '0';
   OBUF2_DST_RDY_N   <= '0';
                
   OBUF3_TXCLK       <= '0';
   OBUF3_TXD         <= (others => '0');
   OBUF3_TXEN        <= '0';
   OBUF3_TXER        <= '0';
   OBUF3_DST_RDY_N   <= '0';

   LBHOLDA	      <= 'Z';
   LBRDY	      <= 'Z';
   LBAD		      <= (others => 'Z');

end architecture empty;

