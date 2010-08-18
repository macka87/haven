-- marker_fl128.vhd: 128b FrameLink cover of FL_MARKER
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- package with FL records
use work.fl_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FL_MARKER_FL128 is
   generic(
      -- Header / Footer data present
      HEADER       : boolean := true;
      FOOTER       : boolean := true;
      -- Mark options
      OFFSET       : integer := 4; -- "Mark" position in FL Header in Bytes
      SIZE         : integer := 1; -- Size of "Mark" in Bytes
      -- Add "mark" to header or footer (only one can be choice)
      MARK_HDR     : boolean := true;
      MARK_FTR     : boolean := false;
      -- architecture switch (false = ReWrite, true = Insert)
      INSERT       : boolean := false
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      MARK           : in  std_logic_vector(SIZE*8-1 downto 0);
      MARK_NEXT      : out std_logic;

      FL_RX          : inout t_fl128;
      FL_TX          : inout t_fl128
   );
end entity FL_MARKER_FL128;


architecture full of FL_MARKER_FL128 is
begin

   FL_MARKER : entity work.FL_MARKER
      generic map(
         DATA_WIDTH        => 128,
         HEADER            => HEADER,
         FOOTER            => FOOTER,
         OFFSET            => OFFSET,
         SIZE              => SIZE,
         MARK_HDR          => MARK_HDR,
         MARK_FTR          => MARK_FTR,
         INSERT            => INSERT
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Add mark interface
         MARK           => MARK,
         MARK_NEXT      => MARK_NEXT,
         -- RX interface
         RX_DATA        => FL_RX.DATA,
         RX_REM         => FL_RX.DREM,
         RX_SOF_N       => FL_RX.SOF_N,
         RX_EOF_N       => FL_RX.EOF_N,
         RX_SOP_N       => FL_RX.SOP_N,
         RX_EOP_N       => FL_RX.EOP_N,
         RX_SRC_RDY_N   => FL_RX.SRC_RDY_N,
         RX_DST_RDY_N   => FL_RX.DST_RDY_N,
         -- TX interface
         TX_DATA        => FL_TX.DATA,
         TX_REM         => FL_TX.DREM,
         TX_SOF_N       => FL_TX.SOF_N,
         TX_EOF_N       => FL_TX.EOF_N,
         TX_SOP_N       => FL_TX.SOP_N,
         TX_EOP_N       => FL_TX.EOP_N,
         TX_SRC_RDY_N   => FL_TX.SRC_RDY_N,
         TX_DST_RDY_N   => FL_TX.DST_RDY_N
      );

end architecture full;
