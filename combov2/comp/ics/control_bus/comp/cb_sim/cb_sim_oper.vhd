-- storage_init_pkg.vhd: Storage Init PKG
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Patrik Beck <beck@liberouter.org>
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
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        STORAGE INIT Declaration
-- ----------------------------------------------------------------------------
package cb_sim_oper is

   -- t_cb_params type
   type t_cb_params is record
      IDENT          : integer;
      BUFFER_SPACE   : integer;
      DATA           : std_logic_vector(127 downto 0);
      TTYPE          : integer;
   end record;

-- function declaration ---------------------------------------

   function cb_packet(ident        : in integer;
                         buffer_space : in integer;
                         data         : in std_logic_vector(15 downto 0)) 
                     return t_cb_params;

   function cb_bm_packet(  ident          :  in integer;
                           t_type         :  in std_logic_vector(3 downto 0);
                           tag            :  in std_logic_vector(11 downto 0);
                           length         :  in std_logic_vector(11 downto 0);
                           local_addr     :  in std_logic_vector(31 downto 0);
                           global_addr    :  in std_logic_vector(63 downto 0)
                           ) return t_cb_params;

end cb_sim_oper;


-- ----------------------------------------------------------------------------
--                      INTERNAL BUS OPERATIONS
-- ----------------------------------------------------------------------------
package body cb_sim_oper is


-- ---------------------------------------------------------------------------
   function cb_packet(ident        : in integer;
                      buffer_space : in integer;
                      data         : in std_logic_vector(15 downto 0))
                     return t_cb_params is
    variable result: t_cb_params;
      begin
      result.IDENT      :=ident;
      result.BUFFER_SPACE :=buffer_space;
      result.DATA(15 downto 0)       :=data;
      result.TTYPE      :=0; -- normal packet
      return result;
    end;


   function cb_bm_packet(  ident          :  in integer;
                           t_type         :  in std_logic_vector(3 downto 0);
                           tag            :  in std_logic_vector(11 downto 0);
                           length         :  in std_logic_vector(11 downto 0);
                           local_addr     :  in std_logic_vector(31 downto 0);
                           global_addr    :  in std_logic_vector(63 downto 0)
                           ) return t_cb_params is

      variable result: t_cb_params;
      begin
         result.IDENT      :=ident;
         result.BUFFER_SPACE := 8; --size of BM packet is 8
         
         result.DATA(11 downto 0)         :=tag;
         result.DATA(15 downto 12)        :=t_type;

         result.DATA(27 downto 16)        :=length;
         result.DATA(31 downto 28)        :="0000";

         result.DATA(63 downto 32)        :=local_addr;
         result.DATA(127 downto 64)       :=global_addr;
         
         result.TTYPE      :=1; -- bm packet
         return result;
      end;



end cb_sim_oper;

