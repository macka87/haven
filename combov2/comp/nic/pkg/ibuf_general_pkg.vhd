-- ibuf_general_pkg.vhd: General IBUF Package
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
--                        General IBUF Package
-- ----------------------------------------------------------------------------
package ibuf_general_pkg is
   
   -- IBUF Status port
   type t_ibuf_general_stat is record
      -- Legth of payload in FL frame generated from actual frame
      PAYLOAD_LEN       : std_logic_vector(15 downto 0);
      -- Incoming protocol error and/or FCS control failed
      FRAME_ERROR       : std_logic; -- 0: OK, 1: Error occured
      CRC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad CRC 
      MAC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad MAC
      LEN_BELOW_MIN     : std_logic; -- 0: OK, 1: Length is below min
      LEN_OVER_MTU      : std_logic; -- 0: OK, 1: Length is over MTU
   end record;

   -- PACODAG interface
   type t_pacodag16 is record
      CLK         : std_logic;
      DATA        : std_logic_vector(15 downto 0);
      DREM        : std_logic_vector(0 downto 0);
      SRC_RDY_N   : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      DST_RDY_N   : std_logic;
      SOP         : std_logic;
      STAT        : t_ibuf_general_stat;
      STAT_DV     : std_logic;
      PACODAG_RDY : std_logic;

   end record;

   type t_pacodag32 is record
      CLK         : std_logic;
      DATA        : std_logic_vector(31 downto 0);
      DREM        : std_logic_vector(1 downto 0);
      SRC_RDY_N   : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      DST_RDY_N   : std_logic;
      SOP         : std_logic;
      STAT        : t_ibuf_general_stat;
      STAT_DV     : std_logic;
      PACODAG_RDY : std_logic;
   end record;

   type t_pacodag64 is record
      CLK         : std_logic;
      DATA        : std_logic_vector(63 downto 0);
      DREM        : std_logic_vector(2 downto 0);
      SRC_RDY_N   : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      DST_RDY_N   : std_logic;
      SOP         : std_logic;
      STAT        : t_ibuf_general_stat;
      STAT_DV     : std_logic;
      PACODAG_RDY : std_logic;
   end record;

   type t_pacodag128 is record
      CLK         : std_logic;
      DATA        : std_logic_vector(127 downto 0);
      DREM        : std_logic_vector(3 downto 0);
      SRC_RDY_N   : std_logic;
      SOP_N       : std_logic;
      EOP_N       : std_logic;
      DST_RDY_N   : std_logic;
      SOP         : std_logic;
      STAT        : t_ibuf_general_stat;
      STAT_DV     : std_logic;
      PACODAG_RDY : std_logic;
   end record;

end ibuf_general_pkg;


-- ----------------------------------------------------------------------------
--                        General Ibuf Package
-- ----------------------------------------------------------------------------
package body ibuf_general_pkg is
       
end ibuf_general_pkg;

