--
-- unpacker_arch.vhd : IB Unpacker Architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_unpacker_pkg.all;

-- ----------------------------------------------------------------------------
--                 ARCHITECTURE DECLARATION  --  IB Unpacker                 --
-- ----------------------------------------------------------------------------

architecture ib_unpacker_arch of IB_UNPACKER is

   -- -------------------------------------------------------------------------
   --                         Constant declaration                           --
   -- -------------------------------------------------------------------------

   constant LENGTH_PARTS_NUM : integer := unpck_length_we_width(DATA_WIDTH);
   constant ADDR_PARTS_NUM   : integer := unpck_addr_we_width(DATA_WIDTH, ADDR_WIDTH);
   constant ALIGN_WIDTH      : integer := unpck_align_width(DATA_WIDTH);

   constant ALIGNZEROES      : std_logic_vector(ALIGN_WIDTH-1 downto 0)    := (others => '0');
   constant ALIGNONES        : std_logic_vector(ALIGN_WIDTH-1 downto 0)    := (others => '1');
   constant ZEROES           : std_logic_vector(128-DATA_WIDTH-1 downto 0) := (others => '0');

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type t_length is array (0 to LENGTH_PARTS_NUM-1) of std_logic_vector(DATA_WIDTH-1 downto 0);

   signal reg_length    : t_length;
   signal reg_addr32    : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal reg_addr64    : std_logic_vector(ADDR_WIDTH-1 downto 0);   
   signal reg_count     : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
   signal reg_tag       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_done_flag : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal LENGTH_aux    : std_logic_vector(11 downto 0);
   signal count_aux2    : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
   signal count_aux1    : std_logic_vector(12 downto 0);
   signal flag4096      : std_logic;
   signal ADDR32_aux    : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal ADDR64_aux    : std_logic_vector(ADDR_WIDTH-1 downto 0);   
   signal TAG_aux       : std_logic_vector(7 downto 0);
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --                            LENGTH REGISTER                             --
   -- -------------------------------------------------------------------------

   -- individual parts of length register -----------------
   reg_lengthp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         for i in 0 to LENGTH_PARTS_NUM-1 loop
            if (LENGTH_WE(i) = '1') then
               reg_length(i) <= DATA;
            end if;
         end loop;               

      end if;
   end process;

   -- length output concatenation -------------------------
   reg_length_concatp: process(reg_length)
   begin
         if (DATA_WIDTH >= 16) then
            LENGTH_aux <= reg_length(0)(15 downto 4);
         end if;

         if (DATA_WIDTH < 16) then
            LENGTH_aux <= reg_length(1)&reg_length(0)(7 downto 4);         
         end if;         
   end process;

   -- length output assignment ----------------------------
   LENGTH    <= LENGTH_aux;
   LEN_ALIGN <= LENGTH_aux(ALIGN_WIDTH-1 downto 0);   

   -- -------------------------------------------------------------------------
   --                             COUNT REGISTER                             --
   -- -------------------------------------------------------------------------

   -- count register --------------------------------------
   reg_countp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         if (HEADER_LAST = '1') then
            reg_count <= count_aux2;
         end if;

         if (COUNT_CE = '1') then
            reg_count <= reg_count - 1;
         end if;         

      end if;
   end process;

   -- count load value ------------------------------------
   count_auxp: process(LENGTH_aux, ADDR64_aux(ALIGN_WIDTH-1 downto 0), count_aux1, DATA, reg_length)
   begin
         if (DATA_WIDTH = 8) then
            if (LENGTH_aux = 0) then flag4096 <= '1'; 
                                else flag4096 <= '0'; end if;
            count_aux1 <= (flag4096 & LENGTH_aux);
            count_aux2 <= count_aux1(12 downto 0);
         elsif (DATA_WIDTH = 128) then
            if (DATA(15 downto 4) = 0) then flag4096 <= '1';               -- mozna misto DATA(15 downto 4) ma byt LENGTH_aux, jako u 64bit 
                                       else flag4096 <= '0'; end if;         
            count_aux1 <= (flag4096 & DATA(15 downto 4)) + DATA(67 downto 64) + "1111";
            count_aux2 <= count_aux1(12 downto ALIGN_WIDTH);
         elsif (DATA_WIDTH = 64) then
            if (LENGTH_aux = 0) then flag4096 <= '1';
                                else flag4096 <= '0'; end if;                  
            count_aux1 <= (flag4096 & LENGTH_aux) + DATA(2 downto 0) + "111";
            count_aux2 <= count_aux1(12 downto ALIGN_WIDTH);            
         else
            if (LENGTH_aux = 0) then flag4096 <= '1'; 
                                else flag4096 <= '0'; end if;         
            count_aux1 <= (flag4096 & LENGTH_aux) + reg_addr64(ALIGN_WIDTH-1 downto 0) + ALIGNONES;
            count_aux2 <= count_aux1(12 downto ALIGN_WIDTH);
         end if;               
   end process;

   -- count output assignment -----------------------------
   COUNT <= reg_count;

   -- -------------------------------------------------------------------------
   --                  (32+ADDR_WIDTH-1):32 ADDRESS REGISTER                 --
   -- -------------------------------------------------------------------------

   -- individual parts of address register ----------------
   reg_addr32p: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         -- write enabling
         for i in 0 to ADDR_PARTS_NUM-1 loop
            if (ADDR32_WE(i) = '1') then
               if (i = ADDR_PARTS_NUM-1 and (ADDR_WIDTH mod DATA_WIDTH /= 0)) then
                  reg_addr32(i*DATA_WIDTH + (ADDR_WIDTH mod DATA_WIDTH) -1 downto i*DATA_WIDTH) <= 
                     unpck_addr32_extracted_from_data(ZEROES&DATA, DATA_WIDTH).VEC((ADDR_WIDTH mod DATA_WIDTH)-1 downto 0);
               else
                  reg_addr32((i+1)*DATA_WIDTH -1 downto i*DATA_WIDTH) <= DATA;
               end if;
            end if;
         end loop;           

         -- count enabling
         if (ADDR32_CE = '1') then
            reg_addr32(work.math_pack.min(ADDR_WIDTH,C_IB_LENGTH_WIDTH)-1 downto log2(DATA_WIDTH/8)) <= 
               reg_addr32(work.math_pack.min(ADDR_WIDTH,C_IB_LENGTH_WIDTH)-1 downto log2(DATA_WIDTH/8)) + 1;
         end if;                                                     -- align_width                                            
         
      end if;
   end process;

   -- addr32 output concatenation -------------------------
   reg_addr32_concatp: process(reg_addr32)
   begin
         if (DATA_WIDTH >= 16) then
            ADDR32_aux <= reg_addr32(ADDR_WIDTH-1 downto ALIGN_WIDTH)&ALIGNZEROES;
         end if;

         if (DATA_WIDTH < 16) then
            ADDR32_aux <= reg_addr32(ADDR_WIDTH-1 downto 0);
         end if;         
   end process;   

   -- address32 output assignment -------------------------
   ADDR32     <= ADDR32_aux;
   A32_ALIGN  <= reg_addr32(ALIGN_WIDTH-1 downto 0);

   -- -------------------------------------------------------------------------
   --                  (64+ADDR_WIDTH-1):64 ADDRESS REGISTER                 --
   -- -------------------------------------------------------------------------

   -- individual parts of address register ----------------
   reg_addr64p: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         -- write enabling
         for i in 0 to ADDR_PARTS_NUM-1 loop
            if (ADDR64_WE(i) = '1') then
               if (i = ADDR_PARTS_NUM-1 and (ADDR_WIDTH mod DATA_WIDTH /= 0)) then
                  reg_addr64(i*DATA_WIDTH + (ADDR_WIDTH mod DATA_WIDTH) -1 downto i*DATA_WIDTH) <= 
                     unpck_addr64_extracted_from_data(ZEROES&DATA, DATA_WIDTH).VEC((ADDR_WIDTH mod DATA_WIDTH)-1 downto 0);
               else
                  reg_addr64((i+1)*DATA_WIDTH -1 downto i*DATA_WIDTH) <= DATA;
               end if;
            end if;
         end loop;           

         -- count enabling
         if (ADDR64_CE = '1') then
            reg_addr64(work.math_pack.min(ADDR_WIDTH,C_IB_LENGTH_WIDTH)-1 downto log2(DATA_WIDTH/8)) <= 
               reg_addr64(work.math_pack.min(ADDR_WIDTH,C_IB_LENGTH_WIDTH)-1 downto log2(DATA_WIDTH/8)) + 1;
         end if;                                                     -- align_width                                        
         
      end if;
   end process;

   -- addr64 output concatenation -------------------------
   reg_addr64_concatp: process(reg_addr64)
   begin
         if (DATA_WIDTH >= 16) then
            ADDR64_aux <= reg_addr64(ADDR_WIDTH-1 downto ALIGN_WIDTH)&ALIGNZEROES;
         end if;

         if (DATA_WIDTH < 16) then
            ADDR64_aux <= reg_addr64(ADDR_WIDTH-1 downto 0);
         end if;         
   end process;   

   -- address64 output assignment -------------------------
   ADDR64     <= ADDR64_aux;
   A64_ALIGN  <= reg_addr64(ALIGN_WIDTH-1 downto 0);   

   -- -------------------------------------------------------------------------
   --                             TAG REGISTER                               --
   -- -------------------------------------------------------------------------   

   -- tag register ----------------------------------------
   reg_tagp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         if (TAG_WE = '1') then
            reg_tag <= DATA;
         end if;

      end if;
   end process;

   -- tag output concatenation ----------------------------
   reg_tag_auxp: process(reg_tag)
   begin
         if (DATA_WIDTH < 32) then
            TAG_aux <= reg_tag(7 downto 0);
         end if;

         if (DATA_WIDTH >= 32) then
            TAG_aux <= reg_tag(23 downto 16);
         end if;         
   end process;

   -- tag output assignment -------------------------------
   TAG <= TAG_aux;

   -- -------------------------------------------------------------------------
   --                            DONE FLAG REGISTER                          --
   -- -------------------------------------------------------------------------   

   -- done flag register ----------------------------------
   reg_done_flagp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         if (DONE_FLAG_WE = '1') then
            reg_done_flag <= DATA;
         end if;

      end if;
   end process;

   -- done flag output assignment -------------------------
   DONE_FLAG <= not reg_done_flag(C_IB_TYPE_CPL);      

end ib_unpacker_arch;

                     

