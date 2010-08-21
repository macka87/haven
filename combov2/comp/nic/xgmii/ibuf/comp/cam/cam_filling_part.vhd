--
-- cam_filling_part.vhd: An important part of CAM responsible for filling
--                       memory rows
-- Copyright (C) 2005-2007 CESNET
-- Author(s): Martin Kosek <xkosek00@stud.fit.vutbr.cz>
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
entity ibuf_cam_filling_part is
   generic(
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer
   );
   port(
      CNT_16            : in std_logic_vector(3 downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      RESET             : in std_logic;
      CLK               : in std_logic;
      DATA_FILL_BUS     : out std_logic_vector(((CAM_ROW_WIDTH / 4) - 1) downto 0)
   );
end entity ibuf_cam_filling_part;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ibuf_cam_filling_part_arch of ibuf_cam_filling_part is

-- ------------------ ibuf_cam_fill_element Component Declaration -------------
component ibuf_cam_fill_element is
   port(
      CNT_IN            : in std_logic_vector(3 downto 0);
      DATA_IN           : in std_logic_vector(3 downto 0);
      DATA_FILL         : out std_logic
   );
end component ibuf_cam_fill_element;


-- ----------------- Constants declaration ------------------------------------
   -- Number of filling elements (ibuf_cam_fill_element)
   constant ELEM_COUNT  : integer := (CAM_ROW_WIDTH / 4);

-- ------------------ Signals declaration -------------------------------------
   signal fill_result      : std_logic_vector((ELEM_COUNT - 1) downto 0);

begin
   DATA_FILL_BUS     <= fill_result;

-- --------- Generating and maping cam_elements -------------------------------
   FILL_ROW: for i in 0 to (ELEM_COUNT - 1) generate
   -- generate all filling elements
      ELEMENT_INST: ibuf_cam_fill_element
         port map (
            CNT_IN         => CNT_16,
            DATA_IN        => DATA_IN((((i + 1) * 4) - 1) downto (i * 4)),
            DATA_FILL      => fill_result(i)
         );
   end generate;


end architecture ibuf_cam_filling_part_arch;
