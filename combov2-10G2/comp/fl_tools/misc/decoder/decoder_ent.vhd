-- decoder_ent.vhd: FrameLink decoder entity
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_DEC is
   generic(
      -- Header data present
      HEADER      : boolean := true;
      -- Footer data present
      FOOTER      : boolean := true
   );
   port(
      CLK         : in  std_logic;
      RESET       : in  std_logic;

      -- FrameLink interface
      SOF_N       : in  std_logic;
      SOP_N       : in  std_logic;
      EOP_N       : in  std_logic;
      EOF_N       : in  std_logic;
      SRC_RDY_N   : in  std_logic;
      DST_RDY_N   : out std_logic;

      -- decoder signals
      SOF         : out std_logic;  -- start of frame
      SOHDR       : out std_logic;  -- start of header
      EOHDR       : out std_logic;  -- end of header
      HDR_FRAME   : out std_logic;  -- header part is transmitted
      SOPLD       : out std_logic;  -- start of payload
      EOPLD       : out std_logic;  -- end of payload
      PLD_FRAME   : out std_logic;  -- payload part is transmitted
      SOFTR       : out std_logic;  -- start of footer
      EOFTR       : out std_logic;  -- end of footer
      FTR_FRAME   : out std_logic;  -- footer part is transmitted
      EOF         : out std_logic;  -- end of frame
      SRC_RDY     : out std_logic;  -- source ready
      DST_RDY     : in  std_logic   -- destination ready
   );
end entity FL_DEC;

