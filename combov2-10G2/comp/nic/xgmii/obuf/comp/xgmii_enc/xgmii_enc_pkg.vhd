-- xgmii_enc_pkg.vhd: Constants used in XGMII ENC component
-- Copyright (C) 2008 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                       XGMII ENC Package
-- ----------------------------------------------------------------------------
package xgmii_enc_pkg is

   -- Output multiplexers control
   constant C_XGMII_ENC_IDLE_IDLE      : std_logic_vector(2 downto 0) := "000";
   constant C_XGMII_ENC_IDLE_PREAMD    : std_logic_vector(2 downto 0) := "001";
   constant C_XGMII_ENC_PREAMU_DATAD   : std_logic_vector(2 downto 0) := "010";
   constant C_XGMII_ENC_DATAU_DATAD    : std_logic_vector(2 downto 0) := "011";
   constant C_XGMII_ENC_PREAMD_PREAMU  : std_logic_vector(2 downto 0) := "100";
   constant C_XGMII_ENC_DATAD_DATAU    : std_logic_vector(2 downto 0) := "101";
   constant C_XGMII_ENC_ERR_ERR        : std_logic_vector(2 downto 0) := "110";
   constant C_XGMII_ENC_DATAU_IDLE     : std_logic_vector(2 downto 0) := "111";

end xgmii_enc_pkg;


-- ----------------------------------------------------------------------------
--                        XGMII ENC Package
-- ----------------------------------------------------------------------------
package body xgmii_enc_pkg is

end xgmii_enc_pkg;

