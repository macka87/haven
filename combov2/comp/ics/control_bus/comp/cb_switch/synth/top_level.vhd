-- top_level.vhd: Control Bus Switch toplevel for synthesis
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
library IEEE;
use IEEE.std_logic_1164.all;
use work.cb_pkg.all; -- Control Bus package
--use work.fl_pkg.all; -- FrameLink package


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB_SWITCH_TOP is
   port(
      
      -- Common Interface
      CB_CLK        : in std_logic;
      CB_RESET      : in std_logic;

      -- Port 0 (Upstream Port)
      PORT0         : inout t_control_bus;
      
      -- Downstream ports
      DS_IN     : in std_logic_vector((5*(16 + 3))-1 downto 0);
      DS_IN_RD  : out std_logic_vector(5-1 downto 0);
      
      DS_OUT    : out std_logic_vector((5*(16 + 3))-1 downto 0);
      DS_OUT_RD : in std_logic_vector(5-1 downto 0)
      
      -- DS_IN, DS_OUT mapping
      -- XXXX  XXXX  XXXX  XXXX  X   X   X    
      -- | -      data      - | sop eop src_rdy
   );
end entity CB_SWITCH_TOP;

ARCHITECTURE synth OF cb_switch_top IS
   begin
   uut: entity work.CB_SWITCH
   generic map(
      DATA_WIDTH     => 16,
      DS_PORTS       => 5
   )
   port map(
      -- Common Control Bus signals
      CB_CLK         => CB_CLK,
      CB_RESET       => CB_RESET,
      
      -- Port 0 (Upstream Port)
      PORT0          => PORT0,
      
      -- Downstream ports
      DS_IN          => DS_IN,
      DS_IN_RD       => DS_IN_RD,
      
      DS_OUT         => DS_OUT,
      DS_OUT_RD      => DS_OUT_RD
   );
end;
