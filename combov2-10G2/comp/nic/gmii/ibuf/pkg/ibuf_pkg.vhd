-- ibuf_pkg.vhd: IBUF Package
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
package ibuf_pkg is
   
   -- IBUF Status port
   type t_ibuf_stat is record
      GMII_ERROR        : std_logic; -- 0: OK, 1: GMII error has occured
      FRAME_LEN         : std_logic_vector(15 downto 0); -- Preamble, SFD, Payload, FCS
      PAYLOAD_LEN       : std_logic_vector(15 downto 0);
      CRC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad CRC
      MAC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad MAC
      LEN_BELOW_MIN     : std_logic; -- 0: OK, 1: Length is below min
      LEN_OVER_MTU      : std_logic; -- 0: OK, 1: Length is over MTU
   end record;

   -- IBUF_RX Status port
   type t_ibuf_rx_stat is record
      GMII_ERROR        : std_logic; -- 0: OK, 1: GMII error has occured
      CRC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad CRC
      FRAME_LEN         : std_logic_vector(15 downto 0); -- Preamble, SFD, Payload, FCS
   end record;

   -- IBUF_BUF Status port
   type t_ibuf_buf_stat is record
      PAYLOAD_LEN       : std_logic_vector(15 downto 0);
      MAC_CHECK_FAILED  : std_logic; -- 0: OK, 1: Bad MAC
      LEN_BELOW_MIN     : std_logic; -- 0: OK, 1: Length is below min
      LEN_OVER_MTU      : std_logic; -- 0: OK, 1: Length is over MTU
   end record;

   -- IBUF commands
   constant IBUFCMD_STROBE_COUNTERS : std_logic_vector(7 downto 0) := X"01";
   constant IBUFCMD_RESET_COUNTERS  : std_logic_vector(7 downto 0) := X"02";
   constant IBUFCMD_SET_SPEED10     : std_logic_vector(7 downto 0) := X"04";
   constant IBUFCMD_SET_SPEED100    : std_logic_vector(7 downto 0) := X"05";
   constant IBUFCMD_SET_SPEED1000   : std_logic_vector(7 downto 0) := X"06";

end ibuf_pkg;


-- ----------------------------------------------------------------------------
--                        FrameLink Package
-- ----------------------------------------------------------------------------
package body ibuf_pkg is
       
end ibuf_pkg;

