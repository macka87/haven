-- cam_sin.vhd: CAM simulation model
-- Copyright (C) 2004 CESNET
-- Author(s): Tobola Jiri    <tobola@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

entity CAM_SIM is

   generic (
      cam_mask       : string;
      cam_data       : string;
      cam_clk_per    : time
   );

   port (

      -- CAM interface
      CD             : inout std_logic_vector(67 downto 0); -- Addr/Data bus
      COP            : in    std_logic_vector(8  downto 0); -- Instruction bus
      COPV           : in    std_logic;            --
      CACK           : inout std_logic;            -- Acknowledge signal
      CEOT           : inout std_logic;            -- End of transfer signal

      CMCLK          : in    std_logic;            -- CAM clock signal
      CPHASE         : in    std_logic;            -- CAM operation phase
      CRST           : in    std_logic;            -- CAM reset signal
      CSEN           : in    std_logic_vector(3 downto 0);

      CMF            : out   std_logic;            -- Matching flags
      CMM            : out   std_logic;
      CMV            : out   std_logic;
      CFF            : out   std_logic
      );

end CAM_SIM;

-- ----------------------------------------------------------------------
--                    Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of cam_sim is

   signal cmf_c         : std_logic;
   signal cmv_c         : std_logic;

   signal flag          : std_logic_vector(3 downto 0);
   signal flag_out      : std_logic;
   signal flag2         : std_logic_vector(3 downto 0);
   signal flag_out2     : std_logic;

   constant camclkper      : time  := cam_clk_per;
   constant CAM_DATA_FILE  : string:= cam_data;
   constant CAM_MASK_FILE  : string:= cam_mask;

begin

-- ---------------------------------------------------------------------
-- -------------------- Cam simulation ---------------------------------
-- ---------------------------------------------------------------------
ceot  <= 'Z';
cmm   <= '0';
cff   <= '0';

cam_op_proc : process
   -- Types definition
   constant CAM_MEM_SIZE  : integer := 1024;
   subtype cam_word_t is std_logic_vector(271 downto 0);
   type cam_memory_t  is array (CAM_MEM_SIZE - 1 downto 0) of cam_word_t;

   -- Variable memory
   variable data      : cam_memory_t;
   variable mask      : cam_memory_t;

   -- CAM result registers
   variable result0      : integer;
   variable result1      : integer;
   variable result2      : integer;
   variable result3      : integer;
   variable info         : integer;
   variable result_idx   : integer;

   -- Auxiliary variables
   variable i            : integer;
   variable l            : line;
   variable wrd          : cam_word_t;
   variable mask_wrd     : cam_word_t;
   variable cam_wrd      : cam_word_t;
   variable aux          : std_logic_vector(67 downto 0);
   variable good         : boolean;

   file inp_data         : text;
   file inp_mask         : text;

begin

   if (CRST = '0') then
      cmf_c <= '0';
      cmv_c <= '0';
      cack  <= 'Z';
      cd    <= (others => 'Z');

      -- ---- Fill CAM - implicit values -----
      for i in 0 to CAM_MEM_SIZE - 1 loop
         data(i) := conv_std_logic_vector(0, 272);
         mask(i) := (others => '1');
      end loop;
      -- ---- Fill data from file -------------
      file_open(inp_data, CAM_DATA_FILE, READ_MODE);
      i:=0;
      while not (endfile(inp_data)) loop
         readline(inp_data, l);
         hread(l, wrd, good);
         data(i) := wrd;
         i:=i+1;
      end loop;
      -- ---- Read mask -----------------------
      file_open(inp_mask, CAM_MASK_FILE, READ_MODE);
      i:=0;
      while not (endfile(inp_mask)) loop
         readline(inp_mask, l);
         hread(l, wrd, good);
         mask(i) := wrd;
         i:=i+1;
      end loop;

      -- ---- Result registers init -----------
      result0 := 0;
      result1 := 1;
      result2 := 2;
      result3 := 3;
      -- ---- Info register -------------------
      info := 1699310848;  -- shoud be 3699310848

      wait until CRST='1';
      wait for camclkper/4;
   else
      cack <= 'Z';
      cd   <= (others => 'Z');
      if copv='1' then
         case cop(1 downto 0) is
            when "00"   =>          -- Read single word
               cmf_c <= '0';
               cmv_c <= '0';
               case cd is
                  when X"00000000000180030" =>
                     aux := conv_std_logic_vector(result0, 68);
                  when X"00000000000180031" =>
                     aux := conv_std_logic_vector(result1, 68);
                  when X"00000000000180032" =>
                     aux := conv_std_logic_vector(result2, 68);
                  when X"00000000000180033" =>
                     aux := conv_std_logic_vector(result3, 68);
                  when X"00000000000180039" =>
                     aux := conv_std_logic_vector(info, 68);
                  when others => aux := X"AAAAAAAAAAAAAAAAA";
               end case;
               wait for camclkper;     -- Wait for
               wait for camclkper;     -- Wait for
               wait for camclkper/2;   -- Wait for
               cack   <= '0';
               wait for camclkper;     -- Wait for ack signal
               cack   <= '1';
               cd     <= aux;
               wait for camclkper;     -- Ack signal
               cack   <= '0';
               cd     <= (others => 'Z');
               wait for camclkper;     -- Idle state
            when "10" =>          -- Searching
               cd <= (others => 'Z');
               wrd(271 downto 204) := cd;
               wait for camclkper/2;
               result_idx := conv_integer(cop(5 downto 4));
               wrd(203 downto 136) := cd;
               wait for camclkper/2;
               wrd(135 downto  68) := cd;
               wait for camclkper/2;
               wrd( 67 downto   0) := cd;

               -- Searching in CAM
               i:=0;
               mask_wrd := mask(i) and wrd;
               cam_wrd  := mask(i) and data(i);
               while not (mask_wrd=cam_wrd or i=CAM_MEM_SIZE) loop
                  mask_wrd := mask(i) and wrd;
                  cam_wrd  := mask(i) and data(i);
                  i:=i+1;
               end loop;
               -- Set result
               wait for camclkper/2;
               cmv_c <= '1', '0' after camclkper;
               if (i = CAM_MEM_SIZE) then
                  cmf_c <= '0';
               else
                  cmf_c <= '1', '0' after camclkper;
               end if;
               i:=i*4;
               case result_idx is
                  when 0 => result0 := i;
                  when 1 => result1 := i;
                  when 2 => result2 := i;
                  when 3 => result3 := i;
                  when others => null;
               end case;
            when others =>          -- Other states
               -- CAM test
               cmf_c   <= '0';
               cmv_c   <= '0';
               wait for 2*camclkper;
         end case;
      else
         cd <= (others => 'Z');
--         cmf_c    <= '0';
--         cmv_c    <= '0';
        wait for camclkper/2;
      end if;
   end if;
end process cam_op_proc;

-- Shift registers
process (CPHASE, CRST, cmf_c)
begin
   if (CPHASE'event and CPHASE='1') then
      if (CRST='0' or cmf_c = 'U') then
         flag <= (others => '0');
      else
         flag <= cmf_c & flag(3 downto 1);
      end if;
   end if;
   flag_out <= flag(0);
end process;

process (CPHASE, CRST, cmv_c)
begin
   if (CPHASE'event and CPHASE='1') then
      if (CRST='0' or cmv_c = 'U') then
         flag2 <= (others => '0');
      else
         flag2 <= cmv_c & flag2(3 downto 1);
      end if;
   end if;
   flag_out2 <= flag2(0);
end process;

cmf <= flag_out;
cmv <= flag_out2;

end architecture behavioral;
-- ----------------------------------------------------
-- ----------------------------------------------------

