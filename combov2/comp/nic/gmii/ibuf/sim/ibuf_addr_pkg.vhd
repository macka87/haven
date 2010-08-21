--
-- ibuf_addr_pkg.vhd: IBUF address package
--
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

use work.ifc_nc_const.all;    -- constants for SFPRO interface card

-- ----------------------------------------------------------------------------
--                      Address Package Declaration
-- ----------------------------------------------------------------------------
package ibuf_addr_pkg is

   -- Base address of multiple components -------------------------------------
   constant IBUF0_OFFSET         : std_logic_vector(31 downto 0) := X"00000000";
   constant IBUF0                : std_logic_vector(31 downto 0) :=
                                   IBUF_BASE_ADDR + IBUF0_OFFSET;

   constant IBUF1_OFFSET         : std_logic_vector(31 downto 0) := X"00000100";
   constant IBUF1                : std_logic_vector(31 downto 0) :=
                                   IBUF_BASE_ADDR + IBUF1_OFFSET;

   constant IBUF2_OFFSET         : std_logic_vector(31 downto 0) := X"00000200";
   constant IBUF2                : std_logic_vector(31 downto 0) :=
                                   IBUF_BASE_ADDR + IBUF2_OFFSET;

   constant IBUF3_OFFSET         : std_logic_vector(31 downto 0) := X"00000300";
   constant IBUF3                : std_logic_vector(31 downto 0) :=
                                   IBUF_BASE_ADDR + IBUF3_OFFSET;
   
   -- Offset and absolute addresses of single component -----------------------
   -- Enable registers
   constant IBUF_ENABLE_OFFSET   : std_logic_vector(31 downto 0) := X"00000020";
   constant IBUF0_ENABLE         : std_logic_vector(31 downto 0) :=
                                   IBUF0 + IBUF_ENABLE_OFFSET;
   constant IBUF1_ENABLE         : std_logic_vector(31 downto 0) :=
                                   IBUF1 + IBUF_ENABLE_OFFSET;
   constant IBUF2_ENABLE         : std_logic_vector(31 downto 0) :=
                                   IBUF2 + IBUF_ENABLE_OFFSET;
   constant IBUF3_ENABLE         : std_logic_vector(31 downto 0) :=
                                   IBUF3 + IBUF_ENABLE_OFFSET;

end ibuf_addr_pkg;

package body ibuf_addr_pkg is
end ibuf_addr_pkg;
