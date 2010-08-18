-- top_level.vhd: Control Bus Endpoint toplevel for synthesis
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
use work.fl_pkg.all; -- FrameLink package


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB_ENDPOINT_TOP is
   generic(
      DATA_WIDTH     : integer := 16;  -- Other than 16 is not supported
      SOURCE_ID      : std_logic_vector(3 downto 0) := "0000";
                                       -- Something like address, unique
      EMPTY_INTERVAL : integer := 8;  -- Resend info about buffer free space
      IN_BUF_SIZE    : integer := 256;   -- Input buffer size, 0 for no buffer
      OUT_BUF_SIZE   : integer := 256; -- Output buffer size, 16-256
      OUT_BUF_MSGS   : integer := 8    -- Maximal number of output messages
                                       -- buffered
   );
   port(
      -- Common Control Bus signals
      CB_CLK         : in std_logic;
      CB_RESET       : in std_logic;
      
      -- TWO Control Bus interfaces
      CB             : inout t_control_bus;

      -- User Component Upstream Interface
      UPS_FL         : inout t_fl16;

      -- User Component Downstream Interface
      DNS_FL         : inout t_fl16
   );
end entity CB_ENDPOINT_TOP;

ARCHITECTURE synth OF cb_endpoint_top IS
   begin
   uut: entity work.CB_ENDPOINT
   generic map(
      DATA_WIDTH     => 16,
      SOURCE_ID      => "0100",
      EMPTY_INTERVAL => 16,
      IN_BUF_SIZE    => 16,
      OUT_BUF_SIZE   => 16,
      OUT_BUF_MSGS   => 4
   )
   port map(
      -- Common Control Bus signals
      CB_CLK         => CB_CLK,
      CB_RESET       => CB_RESET,
      
      -- One Control Bus interface
      CB             => CB,

      -- User Component Upstream Interface
      UPS_FL         => UPS_FL,

      -- User Component Downstream Interface
      DNS_FL         => DNS_FL
   );
end;
