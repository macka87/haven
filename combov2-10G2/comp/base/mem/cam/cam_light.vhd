-- cam_light.vhd: Lightweight CAM
-- Copyright (C) 2009 CESNET
-- Author(s): Martin kosek <kosek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CAM is
   generic (
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer
   );
   port (
      -- common interface
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- insert interface
      ADDR              : in std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
      DATA_IN           : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      WRITE_EN          : in std_logic;
      CLEAR             : in std_logic;
      
      -- search interface
      MATCH_EN          : in std_logic;
      MATCH_BUS         : out std_logic_vector(CAM_ROW_COUNT-1 downto 0);
      MATCH_BUS_VLD     : out std_logic;
      MATCHED           : out std_logic
   );
end entity CAM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture light of CAM is
begin
   CAM_I : entity work.CAM_2PORT
      generic map (
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT
      )
      port map (
         -- common interface
         CLK               => CLK,
         RESET             => RESET,
         -- insert interface
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         WRITE_EN          => WRITE_EN,
         CLEAR             => CLEAR,
         CLEAR_ADDR        => ADDR,
         
         -- search interface
         MATCH_DATA        => DATA_IN,
         MATCH_EN          => MATCH_EN,
         MATCH_BUS         => MATCH_BUS,
         MATCH_BUS_VLD     => MATCH_BUS_VLD,
         MATCHED           => MATCHED
      );

end architecture light;
