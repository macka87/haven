-- cam_init.inc.vhd: CAM operations
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
-- TODO:

-- This macro inserts cam_init procedure which performs CAM initialization.
-- Required procedures: plx_op

-- MACRO START

procedure cam_init(BASE_ADDR : in integer;
                   DATA_FILE : in string; 
                   DATA_WIDTH: in integer) is


   variable result         : t_cmd_parser_ctrl_array;
   file     in_file        : text;
   variable in_line        : line;
   variable address        : integer;
   variable good           : boolean;
   variable data           : std_logic_vector(DATA_WIDTH-1 downto 0);
   variable mask           : std_logic_vector(DATA_WIDTH-1 downto 0);
   variable data_to_write  : std_logic_vector(31 downto 0);

   variable word_count     : integer;

   constant CAM_CMD_OFFSET       : integer := 16#000#;
   constant CAM_STATUS_OFFSET    : integer := 16#040#;
   constant CAM_MASK_OFFSET      : integer := 16#080#;
   constant CAM_DATA_OFFSET      : integer := 16#0C0#;
   constant CAM_ADDR_OFFSET      : integer := 16#100#;
   constant CAM_WRITE_OFFSET     : integer := 16#140#;

   
begin
   result.count := 0;
   word_count := (DATA_WIDTH + 31) / 32;
   
   -- write command, that SW takes control over CAM
   plx_op(plx_write(BASE_ADDR+CAM_CMD_OFFSET, 
      "00000000000000000000000000000010"));
   
   file_open(in_file, DATA_FILE, READ_MODE);
   while not (endfile(in_file)) loop
      readline(in_file, in_line);
         
      read(in_line, address, good);
      hread(in_line, data, good);
      hread(in_line, mask, good);
      assert good report "CAM: CAM_INIT read error" severity ERROR;

      -- write address
      data_to_write:= conv_std_logic_vector(address,32);
      plx_op(plx_write(BASE_ADDR+CAM_ADDR_OFFSET, data_to_write));
      
      -- write data
      for i in 0 to word_count-1 loop
         if i = (word_count - 1) then
            data_to_write := X"00000000";
            data_to_write(DATA_WIDTH-1-i*32 downto 0) := 
               data(DATA_WIDTH-1 downto i*32);
            plx_op(plx_write(BASE_ADDR+CAM_DATA_OFFSET+(i*4), 
               data_to_write));
         else
            plx_op(plx_write(BASE_ADDR+CAM_DATA_OFFSET+(i*4), 
               data(((i+1)*32)-1 downto i*32)));
         end if;
      end loop;

      -- write mask
      for i in 0 to word_count-1 loop
         if i = (word_count - 1) then
            data_to_write := X"00000000";
            data_to_write(DATA_WIDTH-1-i*32 downto 0) := 
               mask(DATA_WIDTH-1 downto i*32);
            plx_op(plx_write(BASE_ADDR+CAM_MASK_OFFSET+(i*4), 
               data_to_write));
         else
            plx_op(plx_write(BASE_ADDR+CAM_MASK_OFFSET+(i*4), 
               mask(((i+1)*32)-1 downto i*32)));
         end if;
      end loop;
      
      -- write data
      data_to_write:=X"00000000";
      plx_op(plx_write(BASE_ADDR+CAM_WRITE_OFFSET, data_to_write));

      -- wait until data are written
      wait for 400 ns;

   end loop;

   -- release control over CAM
   plx_op(plx_write(BASE_ADDR+CAM_CMD_OFFSET, 
      "00000000000000000000000000000000"));

   file_close(in_file);
   
end cam_init;
