-- clk_gen_pkg.vhd: Package for CLK_GEN module
-- Copyright (C) 2009 CESNET
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

package clk_gen_pkg is

   function cv2_clkper (is_125 : boolean) return real;
   function cv2_mult (is_125 : boolean) return integer;

end clk_gen_pkg;

package body clk_gen_pkg is

   function cv2_clkper (is_125 : boolean) return real is
   begin
      if is_125 then
         return 8.0;
      else
         return 4.0;
      end if;
   end cv2_clkper;

   function cv2_mult (is_125 : boolean) return integer is
   begin
      if is_125 then
         return 8;
      else
         return 4;
      end if;
   end cv2_mult;

end clk_gen_pkg;

