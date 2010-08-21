-- phyter_i2c_mi32.vhd: Phyter control & status component - MI32 record cover
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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

use work.lb_pkg.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity PHYTER_I2C_GENERIC is
   generic(
      IFC_CNT  : integer := 4
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- I2C interfaces
      SCL      : inout std_logic_vector(IFC_CNT-1 downto 0);
      SDA      : inout std_logic_vector(IFC_CNT-1 downto 0);

      -- Phyter disable signals
      PHDIS    : out std_logic_vector(IFC_CNT-1 downto 0);

      -- MI32 interface
      MI32     : inout t_mi32
   );
end entity PHYTER_I2C_GENERIC;


-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
architecture full of PHYTER_I2C_GENERIC is
begin

   phyter_norec: entity work.PHYTER_I2C_GENERIC_NOREC
   generic map (
      IFC_CNT     => IFC_CNT
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      -- I2C interfaces
      SCL         => SCL,
      SDA         => SDA,

      -- Phyter disable signals
      PHDIS       => PHDIS,

      -- MI32 interface
      MI32_DWR    => MI32.DWR,
      MI32_ADDR   => MI32.ADDR,
      MI32_RD     => MI32.RD,
      MI32_WR     => MI32.WR,
      MI32_BE     => MI32.BE,
      MI32_DRD    => MI32.DRD,
      MI32_ARDY   => MI32.ARDY,
      MI32_DRDY   => MI32.DRDY
   );

end architecture full;
