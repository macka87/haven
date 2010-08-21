-- fl_watch_addr_pkg.vhd: fl_watch address space
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.addr_space.all;

-- ----------------------------------------------------------------------------
--                      FL_WATCH Address Package Declaration
-- ----------------------------------------------------------------------------
package fl_watch_addr_pkg is

   -- Control register
   constant FL_WATCH_CTRL_OFFSET : std_logic_vector(31 downto 0) := X"00000000";
   constant FL_WATCH_CTRL        : std_logic_vector(31 downto 0) := 
                                   FL_WATCH_BASE_ADDR + FL_WATCH_CTRL_OFFSET;

   -- Offset 0x4 is reserved for future use

   -- Offset of first frame counter
   constant FL_WATCH_FCNT0_OFFSET : std_logic_vector(31 downto 0) := X"00000008";
   constant FL_WATCH_FCNT0        : std_logic_vector(31 downto 0) := 
                                   FL_WATCH_BASE_ADDR + FL_WATCH_FCNT0_OFFSET;

   -- Other addresses are generic, see documentation for details.
   -- (Width of one frame counter is generic, number of these counters is generic
   --  and optionally there are also counters of invalid frames.)

end fl_watch_addr_pkg;

package body fl_watch_addr_pkg is
end fl_watch_addr_pkg;
