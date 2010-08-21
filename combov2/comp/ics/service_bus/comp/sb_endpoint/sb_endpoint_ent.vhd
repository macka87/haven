-- sb_endpoint_ent.vhd: Service Bus Endpoint component entity
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SB_ENDPOINT is
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Service Bus interface
      TDI      : in  std_logic;
      TDI_DV   : in  std_logic;
      TDO      : out std_logic;
      TDO_DV   : out std_logic;

      -- User Component interface
      ADDR     : out std_logic_vector(7 downto 0);
      RD       : out std_logic;
      WR       : out std_logic;
      DWR      : out std_logic_vector(7 downto 0);
      DRD      : in  std_logic_vector(7 downto 0);
      DRDY     : in  std_logic
   );
end entity SB_ENDPOINT;
