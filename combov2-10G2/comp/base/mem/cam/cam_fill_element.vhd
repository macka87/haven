--
-- cam_fill_element.vhd: Basic filling element of CAM.
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_fill_element is
   port(
      CNT_IN         : in std_logic_vector(3 downto 0);
      MASK_IN        : in std_logic_vector(3 downto 0);
      DATA_IN        : in std_logic_vector(3 downto 0);
      DATA_FILL      : out std_logic
   );
end entity cam_fill_element;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_fill_element_arch of cam_fill_element is

-- ------------------ Signals declaration -------------------------------------
   signal and1_out : std_logic_vector(3 downto 0);
   signal and2_out : std_logic_vector(3 downto 0);

begin

and1_out <= CNT_IN and MASK_IN;
and2_out <= DATA_IN and MASK_IN;

-- --------------------------- Comparator -------------------------------------
DATA_FILL <= '1' when (and1_out = and2_out) else '0';

end architecture cam_fill_element_arch;
