-- storage_init_pkg.vhd: Storage Init PKG
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.plx_oper.all;

-- ----------------------------------------------------------------------------
--                        STORAGE INIT Declaration
-- ----------------------------------------------------------------------------
package cmd_parser_oper is

   -- t_cmd_parser_oper type
   type t_cmd_parser_oper is (PLX, WAITING);

   -- t_cmd_parser_ctrl
   type t_cmd_parser_ctrl is record
      OPER        : t_cmd_parser_oper;
      PLX_PARAM   : t_plx_ctrl;
      WAIT_PARAM  : time;
   end record;

   -- t_cmd_parser_ctrl_arr
   type t_cmd_parser_ctrl_arr is array (255 downto 0) of t_cmd_parser_ctrl;

   -- t_cmd_parser_ctrl_array
   type t_cmd_parser_ctrl_array is record
       COMMANDS : t_cmd_parser_ctrl_arr;
       COUNT    : integer;
   end record;
   
   
-- function declaration ---------------------------------------

   procedure cmd_add(cmd_array : inout t_cmd_parser_ctrl_array;
                     cmd       : in t_cmd_parser_ctrl);

   function cmd_read(addr        : in integer;
                     n           : in integer := 1;
                     file_name   : in string := "")
                     return t_cmd_parser_ctrl;

   function cmd_read_noburst(addr    : in integer;
                     n      : in integer := 1)
                     return t_cmd_parser_ctrl;

   function cmd_write(addr : in integer;
                     data : in std_logic_vector(31 downto 0))
                     return t_cmd_parser_ctrl;

   function cmd_write_file(addr        : in integer;
                     file_name   : in string)
                     return t_cmd_parser_ctrl;

   function cmd_write_file_noburst(addr : in integer;
                     file_name   : in string)
                     return t_cmd_parser_ctrl;

   function cmd_wait(wait_time : in time)
                     return t_cmd_parser_ctrl;
   

end cmd_parser_oper;




-- ----------------------------------------------------------------------------
--                        STORAGE INIT Body
-- ----------------------------------------------------------------------------
package body cmd_parser_oper is

-- ----------------------------------------------------------------------------
    procedure cmd_add(cmd_array : inout t_cmd_parser_ctrl_array;
                      cmd       : in t_cmd_parser_ctrl) is
      begin
      cmd_array.COMMANDS(cmd_array.COUNT) := cmd;
      cmd_array.COUNT:=cmd_array.COUNT+1;
    end cmd_add;  
 
-- ---------------------------------------------------------------------------- 
   function cmd_read(addr        : in integer;
                     n           : in integer := 1;
                     file_name   : in string := "")
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=PLX;
      result.PLX_PARAM:=plx_read(addr,n,file_name);
      return result;
    end cmd_read;

    
-- ----------------------------------------------------------------------------
   function cmd_read_noburst(addr    : in integer;
                     n      : in integer := 1)
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=PLX;
      result.PLX_PARAM:=plx_read_noburst(addr,n);
      return result;
    end cmd_read_noburst;

    
-- ----------------------------------------------------------------------------
   function cmd_write(addr : in integer;
                     data : in std_logic_vector(31 downto 0))
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=PLX;
      result.PLX_PARAM:=plx_write(addr,data);
      return result;
    end cmd_write;

    
-- ----------------------------------------------------------------------------
   function cmd_write_file(addr        : in integer;
                     file_name   : in string)
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=PLX;
      result.PLX_PARAM:=plx_write_file(addr,file_name);
      return result;
    end cmd_write_file;      

    
-- ----------------------------------------------------------------------------
   function cmd_write_file_noburst(addr : in integer;
                     file_name   : in string)
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=PLX;
      result.PLX_PARAM:=plx_write_file_noburst(addr,file_name);
      return result;
    end cmd_write_file_noburst;

    
-- ----------------------------------------------------------------------------
   function cmd_wait(wait_time : in time)
                     return t_cmd_parser_ctrl is
      variable result: t_cmd_parser_ctrl;
      begin
      result.OPER:=WAITING;
      result.WAIT_PARAM:=wait_time;
      return result;
    end cmd_wait;                 
end cmd_parser_oper;

