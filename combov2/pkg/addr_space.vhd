-- addr_space.vhd: Address Space Constants
-- Copyright (C) 2008 CESNET
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
--

library IEEE;
use IEEE.std_logic_1164.all;

package addr_space is

   -- ATTENTION! ------------------------------------------------
   -- X"00000000" to X"00020000" and
   -- X"02000000" to X"FFFFFFFF"
   -- are reserved for NetCOPE purposes
   -- use X"00020000" to X"02000000" for application (NetCOPE plugin)

   -- FL_WATCH ------------------------------------------
   constant WATCH_BASE_ADDR : std_logic_vector := X"00010000";
   constant WATCH_LIMIT     : std_logic_vector := X"00010000"; 

end addr_space;

package body addr_space is
end addr_space;

