-- marker.vhd: Implementation of FrameLink header / footer marker
-- Copyright (C) 2007 CESNET
-- Author(s): Michal Trs <trsm1@liberouter.org>
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
-- $Id:
--

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_MARKER is

begin

   assert (false)
      report "This component is buggy, please consult your project leader"
      severity failure;

   -- Insert architecture
   GEN_ARCH_INS:
   if INSERT generate
      FL_MARKER_INS_U: entity work.FL_MARKER_INSERT
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         HEADER         => HEADER,
         FOOTER         => FOOTER,
         OFFSET         => OFFSET,
         SIZE           => SIZE,
         MARK_HDR       => MARK_HDR,
         MARK_FTR       => MARK_FTR
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         MARK           => MARK,
         MARK_NEXT      => MARK_NEXT,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_SOF_N       => RX_SOF_N,
         RX_EOF_N       => RX_EOF_N,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_SOF_N       => TX_SOF_N,
         TX_EOF_N       => TX_EOF_N
   );
   end generate;


   -- Insert architecture
   GEN_ARCH_REWR:
   if not INSERT generate
      FL_MARKER_REWR_U: entity work.FL_MARKER_REWRITE
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         HEADER         => HEADER,
         FOOTER         => FOOTER,
         OFFSET         => OFFSET,
         SIZE           => SIZE,
         MARK_HDR       => MARK_HDR,
         MARK_FTR       => MARK_FTR
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         MARK           => MARK,
         MARK_NEXT      => MARK_NEXT,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_SOF_N       => RX_SOF_N,
         RX_EOF_N       => RX_EOF_N,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_SOF_N       => TX_SOF_N,
         TX_EOF_N       => TX_EOF_N
   );
   end generate;

end architecture full;
