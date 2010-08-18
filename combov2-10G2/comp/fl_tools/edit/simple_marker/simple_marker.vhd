-- simple_marker.vhd: Implementation of simple FrameLink marker
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of SIMPLE_FL_MARKER is

begin

   assert MARK_SIZE > 0 report "MARK_SIZE must be greater than 0" severity failure;
   assert DATA_WIDTH > 0 report "DATA_WIDTH must be greater than 0" severity failure;
   assert PARTS > 0 report "FrameLink with 0 PARTS makes no sense, PARTS must be greater" severity failure;
   assert MARK_PART < PARTS report "MARK_PART must be less than PARTS" severity failure;

   simple_marker_overwrite : 
   if INSERT = false generate
      impl : entity work.SIMPLE_FL_MARKER_OWR
      generic map (
         DATA_WIDTH => DATA_WIDTH,
         OFFSET => OFFSET,
         MARK_SIZE => MARK_SIZE,
         PARTS => PARTS,
         MARK_PART => MARK_PART
      )
      port map (
         CLK => CLK,
         RST => RST,

         MARK => MARK,
         MARK_VALID => MARK_VALID,
         MARK_NEXT => MARK_NEXT,

         RX_DATA => RX_DATA,
         RX_REM => RX_REM,
         RX_SOF_N => RX_SOF_N,
         RX_SOP_N => RX_SOP_N,
         RX_EOF_N => RX_EOF_N,
         RX_EOP_N => RX_EOP_N,
         RX_SRC_RDY_N => RX_SRC_RDY_N,
         RX_DST_RDY_N => RX_DST_RDY_N,

         TX_DATA => TX_DATA,
         TX_REM => TX_REM,
         TX_SOF_N => TX_SOF_N,
         TX_SOP_N => TX_SOP_N,
         TX_EOF_N => TX_EOF_N,
         TX_EOP_N => TX_EOP_N,
         TX_SRC_RDY_N => TX_SRC_RDY_N,
         TX_DST_RDY_N => TX_DST_RDY_N
      );
   end generate;

   simple_marker_insert:
   if INSERT = true generate
      impl : entity work.SIMPLE_FL_MARKER_INS
      generic map (
         DATA_WIDTH => DATA_WIDTH,
         OFFSET => OFFSET,
         MARK_SIZE => MARK_SIZE,
         PARTS => PARTS,
         MARK_PART => MARK_PART
      )
      port map (
         CLK => CLK,
         RST => RST,

         MARK => MARK,
         MARK_VALID => MARK_VALID,
         MARK_NEXT => MARK_NEXT,

         RX_DATA => RX_DATA,
         RX_REM => RX_REM,
         RX_SOF_N => RX_SOF_N,
         RX_SOP_N => RX_SOP_N,
         RX_EOF_N => RX_EOF_N,
         RX_EOP_N => RX_EOP_N,
         RX_SRC_RDY_N => RX_SRC_RDY_N,
         RX_DST_RDY_N => RX_DST_RDY_N,

         TX_DATA => TX_DATA,
         TX_REM => TX_REM,
         TX_SOF_N => TX_SOF_N,
         TX_SOP_N => TX_SOP_N,
         TX_EOF_N => TX_EOF_N,
         TX_EOP_N => TX_EOP_N,
         TX_SRC_RDY_N => TX_SRC_RDY_N,
         TX_DST_RDY_N => TX_DST_RDY_N
      );
   end generate;

end architecture;
