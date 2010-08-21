-- phy_oper.vhd: Phyter Operations
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek martin.mikusek@liberouter.org
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

package phy_oper is
   -- types declaration ------------------------------------------

   -- t_file_name type
   type t_file_name is record
      LEN   : integer;
      ARR   : string(1 to 256);
   end record;

   -- t_phy_oper type
   type t_phy_oper is (INIT, SEND_PACKET, SEND_RAW_PACKET, SEND_TCPDUMP,
                       RECEIVE_PACKET);

   -- t_phy_params type
   type t_phy_params is record
      FILE_NAME      : t_file_name;
      CRC_EN	      : boolean;
      COUNT	         : integer;
      BURST_EN       : boolean;
      TCPDUMP_NOWAIT : boolean;
      SPEED          : integer;
   end record;

   -- t_phy_ctrl type
   type t_phy_ctrl is record
      OPER           : t_phy_oper;
      PARAMS         : t_phy_params;
   end record;

   -- function declaration ---------------------------------------
   function conv_file_name(file_name : string)
                     return t_file_name;

   function conv_fn_string(file_name : t_file_name)
                     return string;

   function init return t_phy_ctrl;

   function send_packet(
          file_name : in string := "";
			 n         : in integer := 1;
			 crc_en    : in boolean := false;
          speed     : in integer := 1000)
			 return t_phy_ctrl;

   function send_raw_packet(
          file_name : in string := "";
			 n         : in integer := 1)
			 return t_phy_ctrl;

   function send_tcpdump(
          file_name : in string := "")
			 return t_phy_ctrl;

    function send_tcpdump_nowait(
          file_name : in string := "")
			 return t_phy_ctrl;

   function receive_packet(
          file_name : in string := "out.txt")
			 return t_phy_ctrl;

   -- -----------------------------------------------------------
end phy_oper;

package body phy_oper is

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
-- function init
-- 
-- Parameters:
--    no parameters
-- 
function init return t_phy_ctrl is
variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper := INIT;
   return phy_ctrl;
end init;

-- ----------------------------------------------------------------
-- function send_packet sends packet from file (adds preamble and crc)
--
-- Parameters:
--       n         - number of words to read (default = 1)
--       file_name - input text file (default = "")
-- 
function send_packet(
          file_name : in string := "";
			 n         : in integer := 1;
			 crc_en    : in boolean := false;
          speed     : in integer := 1000)
			 return t_phy_ctrl is

variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper              := SEND_PACKET;
   phy_ctrl.params.file_name  := conv_file_name(file_name);
   phy_ctrl.params.crc_en     := crc_en;
   phy_ctrl.params.count      := n;
   phy_ctrl.params.burst_en   := false;
   phy_ctrl.params.speed      := speed;
   return phy_ctrl;
end send_packet;

-- function send_raw_packet sends raw packet from file
--
-- Parameters:
--       n         - number of words to read (default = 1)
-- 
function send_raw_packet(
          file_name : in string := "";
			 n         : in integer := 1)
			 return t_phy_ctrl is
variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper              := SEND_RAW_PACKET;
   phy_ctrl.params.file_name  := conv_file_name(file_name);
   phy_ctrl.params.crc_en     := false;
   phy_ctrl.params.count      := n;
   phy_ctrl.params.burst_en   := false;

   return phy_ctrl;
end send_raw_packet;

-- function send_tcpdump sends tcpdump from file
--
-- Parameters:
--       file_name - input text file (default = "")
-- 
function send_tcpdump(
          file_name : in string := "")
			 return t_phy_ctrl is
variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper              := SEND_TCPDUMP;
   phy_ctrl.params.file_name  := conv_file_name(file_name);
   phy_ctrl.params.crc_en     := true;
   phy_ctrl.params.count      := 1;
   phy_ctrl.params.burst_en   := false;
   phy_ctrl.params.tcpdump_nowait  := false;
   return phy_ctrl;
end send_tcpdump;

-- function send_tcpdump sends tcpdump from file
--
-- Parameters:
--       file_name - input text file (default = "")
-- 
function send_tcpdump_nowait(
          file_name : in string := "")
			 return t_phy_ctrl is
variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper              := SEND_TCPDUMP;
   phy_ctrl.params.file_name  := conv_file_name(file_name);
   phy_ctrl.params.crc_en     := true;
   phy_ctrl.params.count      := 1;
   phy_ctrl.params.burst_en   := false;
   phy_ctrl.params.tcpdump_nowait  := true;
   return phy_ctrl;
end send_tcpdump_nowait;

-- function receive_packet saves packet to file
--
-- Parameters:
--       file_name - output text file (default = "out.txt")
-- 
function receive_packet(
          file_name : in string := "out.txt")
			 return t_phy_ctrl is

variable phy_ctrl : t_phy_ctrl;
begin
   phy_ctrl.oper              := RECEIVE_PACKET;
   phy_ctrl.params.file_name  := conv_file_name(file_name);
   phy_ctrl.params.crc_en     := false;
   phy_ctrl.params.count      := 1;
   phy_ctrl.params.burst_en   := false;

   return phy_ctrl;
end receive_packet;

end phy_oper;



