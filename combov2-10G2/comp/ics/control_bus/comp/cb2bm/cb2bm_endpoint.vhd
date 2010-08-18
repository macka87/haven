--
-- cb2bm_endpoint.vhd: CB2BM+CB endpoint top level
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek    <kosek@liberouter.org>
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
use work.math_pack.all;
use work.cb_pkg.all; -- Control Bus package
use work.ib_pkg.all; -- Internal Bus package
use work.fl_pkg.all; -- FrameLink package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB2BM_ENDPOINT is
   generic(
      DATA_WIDTH     : integer := 16;  -- Other than 16 is not supported
      SOURCE_ID      : std_logic_vector(3 downto 0) := "0000";
                                       -- Something like address, unique
      EMPTY_INTERVAL : integer := 4;   -- Resend info about buffer free space
      IN_BUF_SIZE    : integer := 16;  -- Input buffer size, 0 for no buffer
      OUT_BUF_SIZE   : integer := 16;  -- Output buffer size, 16-256
      OUT_BUF_MSGS   : integer := 4    -- Maximal number of output messages
                                       -- buffered
   );
   port(
      CB_CLK         : in  std_logic;
      CB_RESET       : in  std_logic;
      
      -- Control Bus interface
      CB             : inout t_control_bus;

      -- Bus Master interface
      BM             : inout t_ibbm_64
   );
end entity CB2BM_ENDPOINT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB2BM_ENDPOINT_ARCH of CB2BM_ENDPOINT is
   -- ------------------ Signals declaration ----------------------------------
   -- components interconnect signals
   signal ups_fl       : t_fl16;
   signal dns_fl       : t_fl16;

begin

   -- mapping Control Bus endpoint
   CB_ENDPOINT_I : entity work.CB_ENDPOINT
      generic map(
         DATA_WIDTH     => DATA_WIDTH,
         SOURCE_ID      => SOURCE_ID,
         EMPTY_INTERVAL => EMPTY_INTERVAL,
         IN_BUF_SIZE    => IN_BUF_SIZE,
         OUT_BUF_SIZE   => OUT_BUF_SIZE,
         OUT_BUF_MSGS   => OUT_BUF_MSGS
      )
      port map(
         -- Common Control Bus signals
         CB_CLK         => CB_CLK,
         CB_RESET       => CB_RESET,
         -- Control Bus interfaces
         CB             => CB,
         -- User Component Upstream Interface
         UPS_FL         => ups_fl,
         -- User Component Downstream Interface
         DNS_FL         => dns_fl
      );

   -- mapping CB2BM transform component
   CB2BM_I : entity work.CB2BM
      port map(
         CLK            => CB_CLK,
         RESET          => CB_RESET,
         -- Control Bus Endpoint interface
         -- User Component Upstream Interface
         UPS_FL         => ups_fl,
         -- User Component Downstream Interface
         DNS_FL         => dns_fl,
         -- Bus Master Controller interface
         BM             => BM
      );

end architecture CB2BM_ENDPOINT_ARCH;
