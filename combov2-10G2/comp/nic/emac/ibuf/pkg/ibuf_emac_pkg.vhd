-- ibuf_emac_pkg.vhd: Ethernet MAC IBUF Package
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             EMAC IBUF Package
-- ----------------------------------------------------------------------------
package ibuf_emac_pkg is
   
   -- IBUF_RX Status port
   type t_ibuf_emac_rx_stat is record
      -- EMAC receiver statistic vector
      STAT_VECTOR		: std_logic_vector(26 downto 0);
   end record;

   -- Statistic vector important bits
   constant EMAC_STAT_VECTOR_FCS_ERR   : integer := 2;
   constant EMAC_STAT_FRAME_LEN_START  : integer := 18;
   constant EMAC_STAT_FRAME_LEN_END    : integer := 5;

   -- IBUF commands
   constant IBUFCMD_STROBE_COUNTERS 	: std_logic_vector(7 downto 0) := X"01";
   constant IBUFCMD_RESET_COUNTERS  	: std_logic_vector(7 downto 0) := X"02";

end ibuf_emac_pkg;

-- ----------------------------------------------------------------------------
--                        EMAC Ibuf Package Body
-- ----------------------------------------------------------------------------
package body ibuf_emac_pkg is
       
end ibuf_emac_pkg;

