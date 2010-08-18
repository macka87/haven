--
-- phy_sim_xgmii.vhd: PHY - simulation component for XGMII
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
-- NOTE:
--    - INTERFRAME waiting is blocking (during it there cannot be started
--      another operation of both types (RX, TX))
--    - INTERFRAME between packets sended in one operation is ok, but between
--      two operation there is an extra clkper/2 of idle commands (4 octets)
--    - on XGMII, burst mode is not allowed see IEEE 802.3
--    - when receiving packet, it checks only bad pramble (TODO check all errors)
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use ieee.std_logic_textio.all;
use std.textio.all;

use work.phy_oper.all;
use work.crc_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity phy_sim_xgmii is
   generic(
      INTER_FRAME   : integer := 12; -- 96 bit times, see IEEE 802.3
      FILE_NAME_RCV : string  := "";
      -- default value from standard, but for testing frame_toolong check use larger value
      MAX_UNTAGGED_FRAME_SIZE : integer := 1518;
      DEBUG_REPORT  : boolean := false
   );
   port(
      -- TX interface -------------------------------------------------------
      TX_CLK       :  out std_logic;
      TXD          :  out std_logic_vector(31 downto 0) := X"07070707";
      TXC          :  out std_logic_vector(3 downto 0) := "1111";
      -- RX interface -------------------------------------------------------
      RX_CLK       :  in std_logic;
      RXD          :  in std_logic_vector(31 downto 0);
      RXC          :  in std_logic_vector(3 downto 0);
      -- Simulation interface ----------------------------------------------
      OPER        : in    t_phy_oper;
      PARAMS      : in    t_phy_params;
      STROBE      : in    std_logic;
      BUSY        : out   std_logic
   );
end entity phy_sim_xgmii;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of phy_sim_xgmii is

   constant minFrameSize    : integer := 64; --in octets
   constant preambleSize    : integer := 7; --in octets
   constant sfdSize         : integer := 1; --in octets
   constant headerSize      : integer := preambleSize + sfdSize; -- in octets
   constant crc_len         : integer := 4; -- in octets
   constant qTagPrefixSize  : integer := 4; -- in octets
   constant buff_max_length : integer := MAX_UNTAGGED_FRAME_SIZE + headerSize + INTER_FRAME; -- in octets FIXME including crc and TERM ???

   type t_xgmii_data is
      record
         data : std_logic_vector(7 downto 0);
         cmd  : std_logic;
      end record;

   type t_item is array (1 to buff_max_length) of t_xgmii_data;

   type t_buffer is
   record
      item : t_item;
      len   : integer;
   end record;

   type cstream is file of character;

   constant clkper        : time := 6.4 ns; -- 156.25 MHz clock period
   signal   clk		  : std_logic;      -- 156.25 MHz clock

   signal   tx_busy	  : std_logic := '0';
   signal   rx_busy	  : std_logic := '0';

   constant C_XGMII_START : std_logic_vector(7 downto 0) := X"FB";
   constant C_PREAMBLE    : std_logic_vector(7 downto 0) := "01010101";
   constant C_SFD         : std_logic_vector(7 downto 0) := "11010101";
   constant C_XGMII_TERM  : std_logic_vector(7 downto 0) := X"FD";
   constant C_XGMII_IDLE  : std_logic_vector(7 downto 0) := X"07";

   signal   crc_sig       : std_logic_vector(31 downto 0); -- for testing purposes
   signal   sec_sig       : integer;                       -- for testing purposes
   signal   last_usec_sig : integer;                       -- for testing purposes
   signal   usec_sig      : integer;                       -- for testing purposes
   signal   len_sig       : integer;                       -- for testing purposes
   signal   caplen_sig    : integer;                       -- for testing purposes
   signal   wait_half_clk_per_sig : integer;                    -- for testing purposes

begin

-- TX_CLK generation
clk_p: process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

TX_CLK <= clk;

BUSY <= tx_busy or rx_busy;

-- ----------------------------------------------------------------------------
-- -------------------- TX part process  --------------------------------------
-- ----------------------------------------------------------------------------
tx_p : process

-- ------------------ Procedures ----------------------------------------------

-- ----------------------------------------------------------------------------

-- adds data to octets buffer
procedure buff_add(buff : inout t_buffer;
                   data : in std_logic_vector(7 downto 0);
                   cmd  : in std_logic) is
begin
   assert (buff.len < buff_max_length)
      report "buffer overflow" severity ERROR;

   buff.len := buff.len + 1;
   buff.item(buff.len).data := data;
   buff.item(buff.len).cmd := cmd;
end buff_add;

-- adds octets to buffer from line
procedure buff_add_dataline(buff    : inout t_buffer;
                            file in_file : text) is
   variable in_line : line;
   variable i       : integer;
   variable len     : integer;
   variable aux32   : std_logic_vector(31 downto 0);
begin
   readline(in_file, in_line);
   if (in_line'length > 0) then

      assert ((in_line'length > 0) and (in_line'length <= 8) and ((in_line'length mod 2) = 0))
         report "Data are wider than 32bits or not 8bit aligned" severity ERROR;

      len := (in_line'length)/2;

      hread(in_line, aux32((8*len-1) downto 0));

      for i in 0 to (len-1) loop
         buff_add(buff, aux32(((i+1)*8-1) downto (i*8)), '0');
      end loop;
   end if;
end buff_add_dataline;

-- same as above but for raw data
procedure buff_add_rawdataline(buff    : inout t_buffer;
                               file in_file : text) is
   variable in_line : line;
   variable i       : integer;
   variable len     : integer;
   variable aux36   : std_logic_vector(35 downto 0);
begin
   readline(in_file, in_line);
   if (in_line'length > 0) then

      assert (in_line'length = 9)
         report "Data are not 32bit wide" severity ERROR;

      len := (in_line'length - 1)/2;

      hread(in_line, aux36(((8*len-1)+4) downto 0));

      for i in 0 to (len-1) loop
         buff_add(buff, aux36(((i+1)*8-1) downto (i*8)), aux36(32+i));
      end loop;
   end if;
end buff_add_rawdataline;

-- adds preamble to buffer
procedure buff_add_preamble(buff : inout t_buffer) is
begin
   buff_add(buff, C_XGMII_START, '1');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_PREAMBLE, '0');
   buff_add(buff, C_SFD     , '0');
end buff_add_preamble;

-- adds padding to minFrameSize into buffer
procedure buff_add_pad(buff   : inout t_buffer;
                  crc_en : in boolean) is
variable i : integer;
variable pad : integer;
begin
   pad := minFrameSize - (buff.len - 8);
   if (crc_en = true) then
      pad := pad - 4;
   end if;

   while (pad > 0) loop
      buff_add(buff, (others => '0'), '0');
      pad := pad - 1;
   end loop;
end buff_add_pad;

-- compute crc from buffer data specified by first and last indexes
-- and adds crc to buffer
procedure buff_add_crc(buff : inout t_buffer;
                       first : in integer;
                       last  : in integer) is

   variable din8      : std_logic_vector(7 downto 0);
   variable crcreg    : std_logic_vector(31 downto 0) := X"FFFFFFFF";
   variable rn_crcreg : std_logic_vector(31 downto 0);

begin
   for i in first to last loop
      for j in 0 to 7 loop
         din8(j) := buff.item(i).data(7-j);
      end loop;
      crcreg := crc32(crcreg, din8);
   end loop;

   for i in 0 to 31 loop
      rn_crcreg(i) := not crcreg(31-i);
   end loop;

   crc_sig <= rn_crcreg;

   buff_add(buff, rn_crcreg( 7 downto 0 ), '0');
   buff_add(buff, rn_crcreg(15 downto 8 ), '0');
   buff_add(buff, rn_crcreg(23 downto 16), '0');
   buff_add(buff, rn_crcreg(31 downto 24), '0');
end;

-- add interframe waiting (idle) to buffer, extends it to 32 bit align when needed
procedure buff_add_interframe(buff : inout t_buffer) is
begin
   for i in 1 to INTER_FRAME loop
      buff_add(buff, C_XGMII_IDLE, '1');
   end loop;

   -- 32 bit alignment
   while ((buff.len mod 4) /= 0) loop
      buff_add(buff, C_XGMII_IDLE, '1');
   end loop;
end buff_add_interframe;

-- sends buffer into xgmii interface
procedure buff_send(buff : inout t_buffer) is
   variable i : integer := 1;
begin
   assert ((buff.len mod 4) = 0) report "Buffer is not 32bit aligned" severity error;

   while (i <= buff.len) loop
      for j in 0 to 3 loop
         TXD(((j+1)*8-1) downto (j*8)) <= buff.item(i).data;
         TXC(j) <= buff.item(i).cmd;
         i := i + 1;
      end loop;
      wait for clkper/2;
   end loop;
end buff_send;

-- ----------------------------------------------------------------------------
-- procedure send_packet, sends preambule and packet from file to TX interface
-- can compute and send crc
--
-- Parameters:
--       file_name - input text file with one xgmii packet (default = "")
--       n         - number of sended packets (default = 1)
--	      crc_en	 - when true, adds crc after end of packet data (default = false)
-- 
procedure send_packet(file_name : in string := "";
                      n         : in integer := 1;
                      crc_en    : in boolean := false) is
   variable buff      : t_buffer;
   file     in_file   : text;
begin
   buff.len := 0;

   -- open input file
   assert (file_name /= "") report "empty filename" severity ERROR;
   file_open(in_file, file_name, READ_MODE);

   -- -------------------------------------------------------------------------
   -- packet preparation
   -- -------------------------------------------------------------------------

   -- preamble
   buff_add_preamble(buff);

   -- data
   while (not endfile(in_file)) loop
      buff_add_dataline(buff, in_file);
   end loop;

   -- padding
   buff_add_pad(buff, crc_en);

   -- computing crc
   if (crc_en = true) then
      buff_add_crc(buff, headerSize + 1, buff.len);
   end if;

   -- term
   buff_add(buff, C_XGMII_TERM, '1');

   -- interframe (must be aligned to 32bit)
   buff_add_interframe(buff);


   -- packet sending
   for i in 1 to n loop
      buff_send(buff);
   end loop;

   file_close(in_file);

end send_packet;

-- ----------------------------------------------------------------------------
-- procedure send_raw_packet, sends raw packet from file to TX interface
--
-- Parameters:
--    file_name - input text file with one xgmii raw packet (default = "")
--    n         - number of sended packets (default = 1)
--
-- Format:
--    - 9 hexa numbers per line
--    - first hexa number is control
--    - other hexa numbers (8) are data (cannot be unaligned)
--
-- Example:
--
-- 1555555FB -- start and preambule
-- 0D5555555 -- preambule and sfd
-- 029DAFB50 -- data
--

procedure send_raw_packet(file_name : in string := "";
                          n         : in integer := 1) is
   variable buff      : t_buffer;
   file     in_file   : text;

begin
   buff.len := 0;

   -- open input file
   assert (file_name /= "") report "empty filename" severity ERROR;
   file_open(in_file, file_name, READ_MODE);

   -- -------------------------------------------------------------------------
   -- packet preparation
   -- -------------------------------------------------------------------------

   -- data
   while (not endfile(in_file)) loop
      buff_add_rawdataline(buff, in_file);
   end loop;

   -- interframe (must be aligned to 32bit)
   buff_add_interframe(buff);

   -- packet sending
   for i in 1 to n loop
      buff_send(buff);
   end loop;

   file_close(in_file);
end send_raw_packet;

-- ****************************************************************************
procedure read_short(file in_file: cstream; short : out natural) is
   variable res: natural;
   variable c : character;
begin
   if not endfile(in_file) then
      read(in_file, c);
      res := character'pos(c);
      if not endfile(in_file) then
         read(in_file, c);
         res := res + character'pos(c)*256;
         short := res;
      else
         report "unexpected end of file when reading byte" severity ERROR;
      end if;
   else
      report "unexpected end of file when reading byte" severity ERROR;
   end if;
end read_short;

procedure read_int(file in_file: cstream; int_high : out natural; int_low : out natural) is
   --variable res: natural;
   variable tmp: natural;
begin
   read_short(in_file,tmp);
   --report "READ INT: low = " & integer'image(tmp) severity note;
   int_low := tmp;
   read_short(in_file,tmp);
   int_high := tmp;
   --report "READ INT: high = " & integer'image(tmp) severity note;
   --res := res + tmp*256*256;
   --int := res;
end read_int;

-- UNUSED, vhdl does not support long, may be done by fake (low word, hi word)
--procedure read_long(file in_file: cstream; long : out natural) is
--   variable res: natural;
--   variable tmp: natural;
--begin
--   read_int(in_file,tmp);
--   res := tmp;
--   read_int(in_file,tmp);
--   res := res + tmp*256*256*256*256;
--   long := res;
--end read_long;

procedure seek(file in_file: cstream; n : in natural) is
   variable c : character;
   variable i : natural;
begin
   i := n;
   while ((not endfile(in_file)) and (i>0)) loop
      i := i - 1;
      read(in_file, c);
   end loop;
   if (i>0) then
      report "unexpected end of file when seeking" severity ERROR;
   end if;
end seek;

-- ----------------------------------------------------------------------------
-- procedure send_tcpdump, sends preambule and packet data from tcpdump file
-- to TX interface
--
-- Parameters:
--       file_name - input text file with one xgmii packet (default = "")
--       nowait    - use tcpdump timing when false, else inserts only INTER_FRAME
-- Note:
--     - Tere is minimum arrival time difference between two packets one microsecond
--       in tcpdump format. It matches 125 gmii TX_CLK periods.
--     - If there are same arrival times in two packets, procedure inserts INTER_FRAME.
-- 
-- TODO:
--    - add error recovery
procedure send_tcpdump(file_name : in string := ""; nowait : in boolean := false) is
   variable buff        : t_buffer;
   file     in_file     : cstream;
   variable time_sec_l  : natural; -- arrival time
   variable time_sec_h  : natural;
   variable time_usec_l : natural; -- arrival time
   variable time_usec_h : natural; -- arrival time
   variable caplen_l    : natural; -- length of portion present
   variable caplen_h    : natural; -- length of portion present
   variable caplen      : natural; -- length of portion present
   variable len_l       : natural; -- length this packet (off wire)
   variable len_h       : natural; -- length this packet (off wire)
   variable len         : natural; -- length this packet (off wire)
   variable last_sec_l  : natural; -- last arrival time
   variable last_sec_h  : natural; -- last arrival time
   variable last_usec_l : natural; -- last arrival time
   variable last_usec_h : natural; -- last arrival time
   variable c           : character;
   variable sec         : integer; -- wait sec
   variable usec        : integer; -- wait usec
   variable wait_time   : time;
   variable first       : boolean := true;
   variable wait_half_clk_per: integer := 0;
begin

   -- open input file
   assert (file_name /= "") report "empty filename" severity ERROR;
   file_open(in_file, file_name, READ_MODE);

   -- skip file header 24 bytes
   seek(in_file, 24);

   while (not endfile(in_file)) loop
      last_sec_l := time_sec_l;
      last_sec_h := time_sec_h;
      last_usec_l := time_usec_l;
      last_usec_h := time_usec_h;
      
      read_int(in_file, time_sec_h, time_sec_l);
      read_int(in_file, time_usec_h, time_usec_l);
      read_int(in_file, caplen_h, caplen_l);
      read_int(in_file, len_h, len_l);

      len    := len_l;    -- we suppose that length of packet cannot be > (2^16)-1
      caplen := caplen_l; -- we suppose that length of packet cannot be > (2^16)-1

      -- PRINT INFO ABOUT PACKET
      report "time_sec: " & integer'image(time_sec_h) & " " & integer'image(time_sec_l) severity note;
      report "time_usec: " & integer'image(time_usec_h) & " " & integer'image(time_usec_l) severity note;
      report "caplen: " & integer'image(caplen_h) & " " & integer'image(caplen_l) severity note;
      report "len: " & integer'image(len_h) & " " & integer'image(len_l) severity note;
      
      sec := (time_sec_h - last_sec_h)*256*256 + (time_sec_l - last_sec_l);
      usec :=  (time_usec_h - last_usec_h)*256*256 + (time_usec_l - last_usec_l);

      if (caplen /= len) then
         report "uncompleted data of packet in TCPDUMP (caplen!=len)" severity ERROR;
      end if;

      -- waiting for proper packet timing
      if ((first=false) and (nowait=false)) then

         assert ( (sec > 0) or ((sec = 0) and (usec >= 0)) )
                report "Bad timing in tcpdump" severity ERROR;
         wait_half_clk_per :=sec*625000000/2 + usec*625/2 - buff.len/4;

         wait_half_clk_per_sig <= wait_half_clk_per;
         if (wait_half_clk_per > 0) then
            wait for wait_half_clk_per*(clkper/2);
         end if;
      end if;
      first := false;

      -- -------------------------------------------------------------------------
      -- packet preparation
      -- -------------------------------------------------------------------------

      buff.len := 0;
      -- preamble
      buff_add_preamble(buff);

      -- data
      while ((not endfile(in_file)) and (len>0)) loop
         len := len - 1;
         read(in_file, c);
         buff_add(buff,CONV_STD_LOGIC_VECTOR(character'pos(c), 8), '0');
      end loop;
      if (len>0) then
         report "unexpected end of data" severity ERROR;
      end if;

      -- padding
      buff_add_pad(buff, true);

      -- add crc
      buff_add_crc(buff, headerSize + 1, buff.len);

      -- term
      buff_add(buff, C_XGMII_TERM, '1');

      -- interframe
      buff_add_interframe(buff);

      -- packet sending
      buff_send(buff);

      -- setting idle commands
      TXD <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE;
      TXC <= "1111";
   end loop;

   file_close(in_file);
end send_tcpdump;

procedure init is
begin
end init;

-- --------------------- PROCESS BODY -----------------------------------------

begin

   tx_busy   <= '0';
   wait until (clk'event);

   if (STROBE = '1') then
      tx_busy <= '1';
      wait for clkper/4;

      -- Debug report information
      if (DEBUG_REPORT) then
         report "---------------- PHY operation ----------------" severity NOTE;
      end if;

      case OPER is
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Init operation
         when INIT => init;
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Send packet operation
         when SEND_PACKET =>
            send_packet(conv_fn_string(PARAMS.FILE_NAME), PARAMS.COUNT, PARAMS.CRC_EN);
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Send packet operation
         when SEND_TCPDUMP =>
            send_tcpdump(conv_fn_string(PARAMS.FILE_NAME), PARAMS.TCPDUMP_NOWAIT);
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Send raw packet operation
         when SEND_RAW_PACKET =>
            send_raw_packet(conv_fn_string(PARAMS.FILE_NAME), PARAMS.COUNT);
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         when others => null;
      end case;

      tx_busy <= '0';
   end if;

end process;

-- ----------------------------------------------------------------------------
-- -------------------- RX part process  --------------------------------------
-- ----------------------------------------------------------------------------
rx_p : process

-- ------------------ Procedures ----------------------------------------------

-- ----------------------------------------------------------------------------
function term_on_lane(data : in std_logic_vector(31 downto 0);
                      control: in std_logic_vector(3 downto 0)
) return integer is
begin
   -- return true, if there is terminate command
   if (control(0) = '1' and data(7 downto 0) = X"FD") then
      return 0;
   elsif (control(1) = '1' and data(15 downto 8) = X"FD") then
      return 1;
   elsif (control(2) = '1' and data(23 downto 16) = X"FD") then
      return 2;
   elsif (control(3) = '1' and data(31 downto 24) = X"FD") then
      return 3;
   else
      return -1;
   end if;
end;

-- procedure receive_packet saves only correct packet to file -----------------
-- TODO
--   - add saving words limit
--   - write error msg, when packet is shorter than minFrameSize
--   - write error msg, when packet has bad preamble
procedure receive_packet(file_name : in string := "") is

   file     out_file   : text;
   variable out_line   : line;

begin

   -- wait for start command
   wait until (RX_CLK'event and RXC(0) = '1' and RXD(7 downto 0) = X"FB");

   -- open file for write
   file_open(out_file, file_name, WRITE_MODE);

   -- check preamble
   if (RXC = "0001" and RXD = X"555555FB") then
      wait until (RX_CLK'event);
      if (RXC = "0000" and RXD = X"D5555555") then
         wait until (RX_CLK'event);

         -- preamble ok, save data...
         -- TODO add saving words limit
         while (term_on_lane(RXD, RXC) = -1) loop
            hwrite(out_line, RXD);
            writeline(out_file, out_line);
            wait until (RX_CLK'event);
         end loop;

         -- save last data before terminate
         hwrite(out_line, RXD((term_on_lane(RXD, RXC)*8-1) downto 0));
         writeline(out_file, out_line);
      else
         --report "-- bad preamble part2 --";
         write(out_line, string'(""));
         writeline(out_file, out_line);
         write(out_line, string'("-- bad preamble part2 --"));
         writeline(out_file, out_line);
      end if;
   else
      -- report "-- bad preamble part1 --";
      write(out_line, string'(""));
      writeline(out_file, out_line);
      write(out_line, string'("-- bad preamble part1 --"));
      writeline(out_file, out_line);
   end if;

   file_close(out_file);

end receive_packet;

-- --------------------- PROCESS BODY -----------------------------------------

begin

   rx_busy   <= '0';
   wait until (RX_CLK'event);

   if (STROBE = '1') then
      rx_busy <= '1';

      -- Debug report information
      if (DEBUG_REPORT) then
         report "---------------- PHY operation ----------------" severity NOTE;
      end if;

      case OPER is
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Send packet operation
         when RECEIVE_PACKET =>
            receive_packet(conv_fn_string(PARAMS.FILE_NAME));
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         when others => null;
      end case;

      rx_busy <= '0';
   end if;

end process;

-- process saving all received packets
rx_save_p: process

   file     out_file   : text;
   variable out_line   : line;
   variable first      : boolean := true;

function term_on_lane(data : in std_logic_vector(31 downto 0);
                      control: in std_logic_vector(3 downto 0)
                     ) return integer is
begin
   -- return true, if there is terminate command
   if (control(0) = '1' and data(7 downto 0) = X"FD") then
      return 0;
   elsif (control(1) = '1' and data(15 downto 8) = X"FD") then
      return 1;
   elsif (control(2) = '1' and data(23 downto 16) = X"FD") then
      return 2;
   elsif (control(3) = '1' and data(31 downto 24) = X"FD") then
      return 3;
   else
      return -1;
   end if;
end;

begin

   wait until (RX_CLK'event and RXC(0) = '1' and RXD(7 downto 0) = X"FB");

   if (FILE_NAME_RCV /= "") then

      if (first = true) then
         -- open file for write
         file_open(out_file, FILE_NAME_RCV, WRITE_MODE);
         first := false;
      else
         -- open file for append
         file_open(out_file, FILE_NAME_RCV, APPEND_MODE);
         write(out_line, string'(""));
         writeline(out_file, out_line);
      end if;

      -- check preamble
      if (RXC = "0001" and RXD = X"555555FB") then
         wait until (RX_CLK'event);
         if (RXC = "0000" and RXD = X"D5555555") then
            wait until (RX_CLK'event);

            -- preamble ok, save data...
            -- TODO add saving words limit
            while (term_on_lane(RXD, RXC) = -1) loop
               hwrite(out_line, RXD);
               writeline(out_file, out_line);
               wait until (RX_CLK'event);
            end loop;

            -- save last data before terminate
            if (term_on_lane(RXD, RXC) /= 0) then
               hwrite(out_line, RXD((term_on_lane(RXD, RXC)*8-1) downto 0));
               writeline(out_file, out_line);
            end if;
          else
            --report "-- bad preamble part2 --";
            write(out_line, string'(""));
            writeline(out_file, out_line);
            write(out_line, string'("-- bad preamble part2 --"));
            writeline(out_file, out_line);
         end if;
      else
         --report "-- bad preamble part1 --";
         write(out_line, string'(""));
         writeline(out_file, out_line);
         write(out_line, string'("-- bad preamble part1 --"));
         writeline(out_file, out_line);
      end if;

      file_close(out_file);
  end if;

end process;

end architecture behavioral;

