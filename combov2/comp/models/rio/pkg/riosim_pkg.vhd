-- rio_codes.vhd : RocketIO codes package
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera AT liberouter.org>
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

package riosim_pkg is

   constant K28p0 : std_logic_vector(7 downto 0) := X"1C";
   constant K28p1 : std_logic_vector(7 downto 0) := X"3C";  -- comma
   constant K28p2 : std_logic_vector(7 downto 0) := X"5C";
   constant K28p3 : std_logic_vector(7 downto 0) := X"7C";
   constant K28p4 : std_logic_vector(7 downto 0) := X"9C";
   constant K28p5 : std_logic_vector(7 downto 0) := X"BC";  -- comma
   constant K28p6 : std_logic_vector(7 downto 0) := X"DC";
   constant K28p7 : std_logic_vector(7 downto 0) := X"FC";  -- comma
   constant K23p7 : std_logic_vector(7 downto 0) := X"F7";
   constant K27p7 : std_logic_vector(7 downto 0) := X"FB";
   constant K29p7 : std_logic_vector(7 downto 0) := X"FD";
   constant K30p7 : std_logic_vector(7 downto 0) := X"FE";
   constant K_SOP : std_logic_vector(7 downto 0) := K27p7;
   constant K_EOP : std_logic_vector(7 downto 0) := K29p7;
   constant K_ERR : std_logic_vector(7 downto 0) := K30p7;
   constant K_CEX : std_logic_vector(7 downto 0) := K23p7;
   constant IDLE_CORR : std_logic_vector(15 downto 0) := K28p5 & X"C5"; -- corecting IDLE pattern
   constant IDLE_PRES : std_logic_vector(15 downto 0) := K28p5 & X"50"; -- preserving IDLE pattern

   constant IDLE_10B  : std_logic_vector(19 downto 0) := X"A0E89";

   function is_comma
      (
         data   : in std_logic_vector(7 downto 0)
      )
      return boolean; 

   function is_k
      (
         data   : in std_logic_vector(7 downto 0)
      )
      return boolean; 

   function is_10b_idle
      (
         data   : in std_logic_vector(19 downto 0)
      )
      return boolean; 

   function bitvect_mask_match
      (
         data1  : in std_logic_vector(9 downto 0);
         data2  : in bit_vector;
         mask   : in bit_vector
      )
      return boolean;

end riosim_pkg;

package body riosim_pkg is

   -- -------------------------------------------------------------
   
   function is_comma
      (
         data   : in std_logic_vector(7 downto 0)
      )
      return boolean is

   variable result : boolean := false;

   begin
      result := (data = K28p1);
      result := result or (data = K28p5);
      result := result or (data = K28p7);
      
      return result;
      
   end is_comma; 

   -- -------------------------------------------------------------

   function is_k
      (
         data   : in std_logic_vector(7 downto 0)
      )
      return boolean is

   variable result : boolean := false;

   begin
      result := is_comma(data);
      result := result or (data = K28p0);
      result := result or (data = K28p2);
      result := result or (data = K28p3);
      result := result or (data = K28p4);
      result := result or (data = K28p6);
      result := result or (data = K23p7);
      result := result or (data = K27p7);
      result := result or (data = K29p7);
      result := result or (data = K30p7);
      
      return result;
      
   end is_k; 

   -- -------------------------------------------------------------

   function is_10b_idle
      (
         data   : in std_logic_vector(19 downto 0)
      )
      return boolean is

   begin
      if (data = X"5F2B6" or data = X"A0E89" or data = X"5F289" or data = X"A0EB6") then -- IDLE pattern variations
         return true;
      else 
         return false;
      end if;
   end is_10b_idle; 

   -- -------------------------------------------------------------

   function bitvect_mask_match
      (
         data1  : in std_logic_vector(9 downto 0);
         data2  : in bit_vector;
         mask   : in bit_vector
      )
      return boolean is

   variable result : boolean := true;

   begin
      for i in 0 to 9 loop
         if (mask(i) = '1') then
            -- that stupid VDHL can't simply compare std_logic_vector's bit and bit_vector's bit :(
            if ((data1(i) = '1' and data2(i) = '1') or (data1(i) = '0' and data2(i) = '0')) then
               result := result;
            else
               result := false;
            end if;
         end if;
      end loop;
      return result;
      
   end bitvect_mask_match; 

end riosim_pkg;

