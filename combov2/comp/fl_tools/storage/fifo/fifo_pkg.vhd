-- fl_fifo_pkg.vhd: Package with function
-- Copyright (C) 2003 CESNET
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
-- TODO:
--
-- ------------------------------------------------------------------
--                   Package Interface
-- ------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;

package fl_fifo_pkg is

   function get_juice_width(data_width:integer;use_brams:boolean)return integer;

   function get_bram_type(data_width:integer) return integer;

end fl_fifo_pkg;

-- ------------------------------------------------------------------
--                   Package Body
-- ------------------------------------------------------------------
package body fl_fifo_pkg is

   function min(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;

   -- ----------------------------------------------------------------------
   function get_juice_width(data_width:integer;use_brams:boolean)return
   integer is
   begin
      if use_brams = true then
         return min(data_width/16, 4);
      else
         return 4;
      end if;
   end;
   
   -- ----------------------------------------------------------------------
   function get_bram_type(data_width:integer) return integer is
   begin
      if data_width = 16 then
         return 18;
      else 
         return 36;
      end if;
   end;
end fl_fifo_pkg;
