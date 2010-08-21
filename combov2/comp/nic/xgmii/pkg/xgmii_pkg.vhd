-- xgmii_pkg.vhd: XGMII protocol constants
-- Copyright (C) 2007 CESNET
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

library IEEE;
use IEEE.std_logic_1164.all;

package XGMII_PKG is
   -- constant declaration
   constant C_XGMII_IDLE        : std_logic_vector := X"07";
   constant C_XGMII_SEQUENCE    : std_logic_vector := X"9C";
   constant C_XGMII_SOP         : std_logic_vector := X"FB";
   constant C_XGMII_TERMINATE   : std_logic_vector := X"FD";
   constant C_XGMII_ERROR       : std_logic_vector := X"FE";

   constant C_SEQ_LINK_DOWN_D   : std_logic_vector(31 downto 0) :=
         X"010000" & C_XGMII_SEQUENCE;
   constant C_SEQ_LINK_DOWN_C   : std_logic_vector(3 downto 0) :=
         "0001";

   constant C_XGMII_IDLE_WORD64 : std_logic_vector(63 downto 0) :=
         C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
         C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE;

   -- Preamble in XGMII protocol
   constant C_PREAMBLE          : std_logic_vector(63 downto 0) :=
                                          X"D5555555555555" & C_XGMII_SOP;
end XGMII_PKG;

package body XGMII_PKG is
end XGMII_PKG;

