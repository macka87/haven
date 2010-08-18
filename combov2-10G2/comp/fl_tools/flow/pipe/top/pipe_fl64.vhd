--
-- pipe_fl64.vhd: 64bit FrameLink cover of FrameLink Pipe
--
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity fl_pipe_fl64 is
   port (
      CLK   : in std_logic;
      RESET : in std_logic;

      -- input interface
      RX    : inout t_fl64;
      
      -- output interfaces
      TX    : inout t_fl64
   );
end entity fl_pipe_fl64;

architecture full of fl_pipe_fl64 is
begin

   fl_pipe_u: entity work.fl_pipe
   generic map (
      DATA_WIDTH     => 64
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      RX_DATA        => RX.DATA,
      RX_REM         => RX.DREM,
      RX_SOF_N       => RX.SOF_N,
      RX_SOP_N       => RX.SOP_N,
      RX_EOP_N       => RX.EOP_N,
      RX_EOF_N       => RX.EOF_N,
      RX_SRC_RDY_N   => RX.SRC_RDY_N,
      RX_DST_RDY_N   => RX.DST_RDY_N,
      
      -- output interface
      TX_DATA        => TX.DATA,
      TX_REM         => TX.DREM,
      TX_SOF_N       => TX.SOF_N,
      TX_SOP_N       => TX.SOP_N,
      TX_EOP_N       => TX.EOP_N,
      TX_EOF_N       => TX.EOF_N,
      TX_SRC_RDY_N   => TX.SRC_RDY_N,
      TX_DST_RDY_N   => TX.DST_RDY_N
   );

end architecture full;
