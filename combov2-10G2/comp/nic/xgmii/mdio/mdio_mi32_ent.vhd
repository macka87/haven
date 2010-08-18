-- mdio_ent.vhd MDIO design interface (entity) - MI32
-- Copyright (C) 2003-2009 CESNET
-- Author(s): Michal Janousek <xjanou11@stud.fit.vutbr.cz>
--            Libor Polcak <polcak_l@liberouter.org>
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
entity mdio_ctrl_mi32 is

   port (
      -- Common interface
      RESET    : in    std_logic;
      CLK      : in    std_logic; -- 50MHz or 100MHz

      -- Mdio interface
      MDC      : out std_logic; -- MDIO Clock output
      MDIO_I   : in  std_logic; -- MDIO Input data
      MDIO_O   : out std_logic; -- MDIO Output data
      MDIO_OE  : out std_logic; -- MDIO Output Enable, active low

      -- MI32 interface
      -- Input Data
      MI_DWR            : in  std_logic_vector(31 downto 0);
      -- Address
      MI_ADDR           : in  std_logic_vector(31 downto 0);
      -- Read Request
      MI_RD             : in  std_logic;
      -- Write Request
      MI_WR             : in  std_logic;
      -- Byte Enable
      MI_BE             : in  std_logic_vector(3  downto 0);
      -- Output Data
      MI_DRD            : out std_logic_vector(31 downto 0);
      -- Address Ready
      MI_ARDY           : out std_logic;
      -- Data Ready
      MI_DRDY           : out std_logic

   );
end mdio_ctrl_mi32;

