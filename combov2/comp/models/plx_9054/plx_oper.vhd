-- plx_oper.vhd: Local Bus Operations
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
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

package plx_oper is
   -- types declaration ------------------------------------------

   -- t_file_name type
   type t_file_name is record
      LEN   : integer;
      ARR   : string(1 to 256);
   end record;

   -- t_plx_status type
   type t_plx_status is record
      DO    : std_logic_vector(31 downto 0);
      DV    : std_logic;
   end record;

   -- t_plx_oper type
   type t_plx_oper is (INIT, READ, WRITE_DATA, WRITE_FILE);

   -- t_plx_params type
   type t_plx_params is record
      ADDR           : integer;
      COUNT          : integer;
      FILE_NAME      : t_file_name;
      DATA           : std_logic_vector(31 downto 0);
      NO_BURST       : boolean;
   end record;

   -- t_plx_ctrl type
   type t_plx_ctrl is record
      OPER           : t_plx_oper;
      PARAMS         : t_plx_params;
   end record;
   
   -- t_plx_ctrl array type
   type t_plx_ctrl_arr is array (255 downto 0) of t_plx_ctrl;

   -- t_plx_ctrl array type with count
   type t_plx_ctrl_array is record
       COMMANDS : t_plx_ctrl_arr;
       COUNT    : positive;
   end record;
   
   -- function declaration ---------------------------------------
   function conv_file_name(file_name : string)
                     return t_file_name;

   function conv_fn_string(file_name : t_file_name)
                     return string;

   function plx_init return t_plx_ctrl;

   function plx_read(addr        : in integer;
                     n           : in integer := 1;
                     file_name   : in string := "")
                     return t_plx_ctrl;

   function plx_read_noburst(addr    : in integer;
                     n      : in integer := 1)
                     return t_plx_ctrl;

   function plx_write(addr : in integer;
                     data : in std_logic_vector(31 downto 0))
                     return t_plx_ctrl;

   function plx_write_file(addr        : in integer;
                     file_name   : in string)
                     return t_plx_ctrl;

   function plx_write_file_noburst(addr : in integer;
                     file_name   : in string)
                     return t_plx_ctrl;

   -- -----------------------------------------------------------
end plx_oper;

package body plx_oper is

-- ----------------------------------------------------------------
-- function conv_file_name converts string type into the t_file_name
-- type
-- 
-- Parameters:
--    file_name : filename in string format
-- 
function conv_file_name(file_name : string) return t_file_name is
variable result : t_file_name;
begin
   result.len := file_name'length;
   result.arr(1 to result.len) := file_name;
   return result;
end;

-- ----------------------------------------------------------------
-- function conv_fn_file_name converts t_file_name type into the string
-- type
-- 
-- Parameters:
--    file_name : filename in t_file_name format
-- 
function conv_fn_string(file_name : t_file_name) return string is
begin
   return file_name.arr(1 to file_name.len);
end;

-- ----------------------------------------------------------------
-- function plx_init makes control structure for initialization
-- of local bus signals and setting lreset signals,
-- 
-- Parameters:
--    no parameters
-- 
function plx_init return t_plx_ctrl is
variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper := INIT;
   return plx_ctrl;
end plx_init;

-- ----------------------------------------------------------------

-- function plx_read makes control structure for reading 'n' words
-- from local bus at address 'addr', and saveing data to file, if
-- parameter 'file_name' is set
--
-- Parameters:
--       addr     - start read address
--       n        - number of words to read (default = 1)
--       file_name- output text file (default = "")
-- 
function plx_read(addr        : in integer;
                 n           : in integer := 1;
                 file_name   : in string := "") return t_plx_ctrl is

variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper              := READ;
   plx_ctrl.params.addr       := addr;
   plx_ctrl.params.count      := n;
   plx_ctrl.params.file_name  := conv_file_name(file_name);
   plx_ctrl.params.no_burst   := false;
   return plx_ctrl;
end plx_read;

-- ----------------------------------------------------------------
-- function plx_read_noburst makes control structure for reading
-- 'n' words from local bus at address 'addr'
--
-- Parameters:
--       addr     - start read address
--       n        - number of words to read (default = 1)
-- 
function plx_read_noburst(addr    : in integer;
                          n      : in integer := 1) return t_plx_ctrl is
variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper              := READ;
   plx_ctrl.params.addr       := addr;
   plx_ctrl.params.count      := n;
   plx_ctrl.params.no_burst   := true;
   return plx_ctrl;
end plx_read_noburst;

-- ----------------------------------------------------------------
-- function plx_write makes control structure for writing one word of
-- data 'data' to address 'addr'
--
-- Parameters:
--       addr     - start address to write
--       data     - input data
--
function plx_write(addr : in integer;
                  data : in std_logic_vector(31 downto 0)) return t_plx_ctrl is
variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper              := WRITE_DATA;
   plx_ctrl.params.addr       := addr;
   plx_ctrl.params.data       := data;
   return plx_ctrl;
end plx_write;

-- ----------------------------------------------------------------
-- function plx_write_file makes control structure for writing data
-- from file 'file_name' to local bus at address 'addr'
--
-- Parameters:
--       addr     - start address to write
--       file_name- file name of input data
--
function plx_write_file(addr        : in integer;
                       file_name   : in string) return t_plx_ctrl is
variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper              := WRITE_FILE;
   plx_ctrl.params.addr       := addr;
   plx_ctrl.params.file_name  := conv_file_name(file_name);
   plx_ctrl.params.no_burst   := false;
   return plx_ctrl;
end plx_write_file;

-- ----------------------------------------------------------------
-- function plx_write_file_noburst makes control structure for writing
-- data from file 'file_name' to local bus at address 'addr' not
-- in burst mode
--
-- Parameters:
--       addr     - start address to write
--       file_name- file name of input data
--
function plx_write_file_noburst(addr : in integer;
                        file_name   : in string) return t_plx_ctrl is
variable plx_ctrl : t_plx_ctrl;
begin
   plx_ctrl.oper              := WRITE_FILE;
   plx_ctrl.params.addr       := addr;
   plx_ctrl.params.file_name  := conv_file_name(file_name);
   plx_ctrl.params.no_burst   := true;
   return plx_ctrl;
end plx_write_file_noburst;


end plx_oper;

