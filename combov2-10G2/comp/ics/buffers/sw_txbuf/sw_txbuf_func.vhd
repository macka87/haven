-- swt_func.vhd: Auxiliary functions for SW_TXBUF
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


library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Package declaration
-- ----------------------------------------------------------------------------
package SWT_FUNC is

   -- ------------------ Functions declaration --------------------------------
   function swt_if_else (
      cond        : boolean; 
      if_true     : integer; 
      if_false    : integer
      )
   return integer;


end SWT_FUNC;

-- ----------------------------------------------------------------------------
--                      Package body declaration
-- ----------------------------------------------------------------------------

package body SWT_FUNC is

   -- -------------------------------------------------------------------------
   function swt_if_else (
      cond        : boolean; 
      if_true     : integer; 
      if_false    : integer
      )
   return integer is
   
   begin
      if (cond) then
         return if_true;
      else
         return if_false;
      end if;
   end function swt_if_else;

end SWT_FUNC;
