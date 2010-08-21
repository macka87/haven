-- fl_pkg.vhd: FrameLink Package
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.cz>
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
-- $$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        FrameLink Package
-- ----------------------------------------------------------------------------
package fl_pkg is

   -- FrameLink - data width 8 - no DREM signal
   type t_fl8 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic; 
      DATA        : std_logic_vector(7 downto 0);
   end record; 

   -- FrameLink - data width 16
   type t_fl16 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic; 
      DATA        : std_logic_vector(15 downto 0);
      DREM        : std_logic_vector(0 downto 0);
   end record;

   -- FrameLink - data width 32
   type t_fl32 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic; 
      DATA        : std_logic_vector(31 downto 0);
      DREM        : std_logic_vector(1 downto 0); 
   end record;

   -- FrameLink - data width 64 
   type t_fl64 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic; 
      DATA        : std_logic_vector(63 downto 0);
      DREM        : std_logic_vector(2 downto 0); 
   end record;

   -- FrameLink - data width 128
   type t_fl128 is record
      SOF_N       : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      EOF_N       : std_logic;
      SRC_RDY_N   : std_logic;
      DST_RDY_N   : std_logic; 
      DATA        : std_logic_vector(127 downto 0);
      DREM        : std_logic_vector(3 downto 0); 
   end record;

end fl_pkg;


-- ----------------------------------------------------------------------------
--                        FrameLink Package
-- ----------------------------------------------------------------------------
package body fl_pkg is
       
end fl_pkg;

