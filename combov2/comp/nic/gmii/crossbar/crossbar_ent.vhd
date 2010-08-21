--
-- crossbar_ent.vhd : Crossbar for gmii interface.
-- Copyright (C) 2007 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Internal bus package
use work.lb_pkg.all;

-- Math package - log2 function
use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


entity CROSSBAR is
   generic(
      PORTS   : natural := 4; -- number of ports (DOES have both TX and RX parts)
      INPUTS  : natural := 4; -- number of inputs (only RX part)
      OUTPUTS : natural := 4  -- number of outputs (only TX part)
   );

   port (
      RESET : in std_logic; -- reset

      --*** PORTS INTERFACE ***--
      -- GMII Interface (input ports)
      P_RXD   : in std_logic_vector((8*PORTS)-1 downto 0); -- RX data
      P_RXDV  : in std_logic_vector(PORTS-1 downto 0);     -- RX data valid
      P_RXER  : in std_logic_vector(PORTS-1 downto 0);     -- RX error

      -- GMII Interface (output ports)
      P_TXD   : out std_logic_vector((8*PORTS)-1 downto 0); -- outGMII transmitt data
      P_TXEN  : out std_logic_vector(PORTS-1 downto 0);     -- GMII transmit enable
      P_TXER  : out std_logic_vector(PORTS-1 downto 0);     -- GMII transmit error


      --*** DESIGN INTERFACE ***--
      -- GMII Interface (input)
      I_RXD   : in std_logic_vector((8*INPUTS)-1 downto 0); -- RX data
      I_RXDV  : in std_logic_vector(INPUTS-1 downto 0);     -- RX data valid
      I_RXER  : in std_logic_vector(INPUTS-1 downto 0);     -- RX error 

      -- GMII Interface (output)
      O_TXD   : out std_logic_vector((8*OUTPUTS)-1 downto 0); -- outGMII transmitt data
      O_TXEN  : out std_logic_vector(OUTPUTS-1 downto 0);     -- GMII transmit enable
      O_TXER  : out std_logic_vector(OUTPUTS-1 downto 0);     -- GMII transmit error

      -- Local Bus Interface
      CLK   : in std_logic; -- design clock (supposed to be local bus clock)
      MI32  : inout t_mi32  -- MI32 interface

   );
end entity;
