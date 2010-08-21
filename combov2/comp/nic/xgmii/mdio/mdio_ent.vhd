-- mdio_ent.vhd MDIO design interface (entity)
-- Copyright (C) 2003 CESNET
-- Author(s): Michal Janousek <xjanou11@stud.fit.vutbr.cz>
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
use IEEE.STD_LOGIC_1164.ALL;

-- -------------------------------------------------------
--                 Entity declaration
-- -------------------------------------------------------
entity mdio_ctrl is
   generic(
      BASE           : integer;
      ADDR_WIDTH     : integer
   );
   port (
      -- Common interface
      RESET    : in    std_logic;
      CLK      : in    std_logic; -- 50MHz or 100MHz

      -- Mdio interface
      MDC      : out   std_logic;
      MDIO     : inout std_logic;

      -- Local bus interface
      LBCLK    : in    std_logic;
      LBFRAME  : in    std_logic;
      LBAS     : in    std_logic;
      LBRW     : in    std_logic;
      LBLAST   : in    std_logic;
      LBAD     : inout std_logic_vector(15 downto 0);
      LBHOLDA  : out   std_logic;
      LBRDY    : out   std_logic
   );
end mdio_ctrl;

