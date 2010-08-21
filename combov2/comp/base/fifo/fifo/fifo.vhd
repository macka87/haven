--
-- fifo.vhd: FIFO - m x n bit
--                - synchronous write, asynchronous read
-- Copyright (C) 2003 CESNET
-- Author(s):  Pecenka Tomas pecenka@liberouter.org
--             Pus Viktor    pus@liberouter.org
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
use work.math_pack.all;

-- auxilary functions and constant needed to evaluate generic address etc.
use WORK.distmem_func.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture fifo_arch of fifo is

   constant ADDRESS_WIDTH  : integer := LOG2(ITEMS);

   component dp_distmem is
      generic(
         DISTMEM_TYPE : integer;
         DATA_WIDTH   : integer;
         ITEMS        : integer
      );
      port (
         RESET    : in std_logic;
         -- Write port
         WCLK     : in std_logic;
         ADDRA    : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
         DI       : in std_logic_vector(DATA_WIDTH-1 downto 0);
         WE       : in std_logic;
         DOA      : out std_logic_vector(DATA_WIDTH-1 downto 0);

         -- Read port
         ADDRB    : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
         DOB      : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
   end component dp_distmem;

   -- Read and write address signals
   signal read_address  : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal write_address : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   -- Signals for read and write address counters
   signal cnt_write_address : std_logic_vector(ADDRESS_WIDTH downto 0);
   signal cnt_read_address  : std_logic_vector(ADDRESS_WIDTH downto 0);

   -- Read and write address registers
   signal reg_write_address : std_logic_vector(ADDRESS_WIDTH downto 0);
   signal reg_read_address  : std_logic_vector(ADDRESS_WIDTH downto 0);

   -- Address comparators
   signal cmp_empty : std_logic;
   signal cmp_full  : std_logic;

   -- Read and Write operation from/to FIFO allowed signal
   signal sig_write_allowed : std_logic;
   signal sig_read_allowed  : std_logic;
   signal sig_empty_full_we : std_logic;

   -- FULL and EMPY internal signals
   signal reg_full   : std_logic;
   signal reg_empty  : std_logic;
   signal reg_lstblk : std_logic;
   signal sig_full   : std_logic;
   signal sig_empty  : std_logic;

   -- last block signals
   signal cnt_diff            : std_logic_vector(ADDRESS_WIDTH downto 0);
   signal cnt_diff_ce         : std_logic;
   signal cnt_diff_dir        : std_logic;
   signal lstblk_plus_one     : std_logic;
   signal lstblk_minus_one     : std_logic;

begin
   -- Actual write address
   write_address <= reg_write_address(ADDRESS_WIDTH-1 downto 0);
   -- Actual read address
   read_address <= reg_read_address(ADDRESS_WIDTH-1 downto 0);

   -- Memory connection -------------------------------------------------------
   U_DP_DISTMEM: DP_DISTMEM
      generic map (
         distmem_type   => DISTMEM_TYPE,
         data_width     => DATA_WIDTH,
         items          => ITEMS
      )
      port map (
         RESET       => RESET,
         -- Write port
         WCLK        => CLK,
         ADDRA       => write_address,
         DI          => DATA_IN,
         WE          => sig_write_allowed,
         DOA         => open,

         -- Read port
         ADDRB       => read_address,
         DOB         => DATA_OUT
      );

   -- register reg_write_address ----------------------------------------------
   reg_write_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_write_address <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (sig_write_allowed = '1') then
            reg_write_address <= cnt_write_address;
         end if;
      end if;
   end process;

   -- Write address counter ---------------------------------------------------
   cnt_write_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_write_address <=
               conv_std_logic_vector(1, cnt_write_address'length);
      elsif (CLK'event AND CLK = '1') then
         if (sig_write_allowed = '1') then
            cnt_write_address <= cnt_write_address + 1;

            if (cnt_write_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_write_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
               cnt_write_address(ADDRESS_WIDTH) <=
                     not cnt_write_address(ADDRESS_WIDTH);
            end if;

         end if;
      end if;
   end process;

   -- register reg_read_address ------------------------------------------------------
   reg_read_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_read_address <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (sig_read_allowed = '1') then
            reg_read_address <= cnt_read_address;
         end if;
      end if;
   end process;

   -- Read counter ------------------------------------------------------------
   cnt_read_addressp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_read_address <=
               conv_std_logic_vector(1, cnt_read_address'length);
      elsif (CLK'event AND CLK = '1') then
         if (sig_read_allowed = '1') then
            cnt_read_address <= cnt_read_address + 1;

            if (cnt_read_address(ADDRESS_WIDTH-1 downto 0) = ITEMS-1) then
               cnt_read_address(ADDRESS_WIDTH-1 downto 0) <= (others => '0');
               cnt_read_address(ADDRESS_WIDTH) <=
                     not cnt_read_address(ADDRESS_WIDTH);
            end if;

         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
-- CONTROL LOGIC
-- ----------------------------------------------------------------------------

   -- Read and Write allowed signals
   sig_write_allowed <= WRITE_REQ and not reg_full;
   sig_read_allowed  <= READ_REQ  and not reg_empty;

   sig_empty_full_we <= sig_read_allowed or sig_write_allowed;


   -- Comparator for EMPTY signal ---------------------------------------------
   cmp_emptyp: process(cnt_read_address, reg_write_address)
   begin
      cmp_empty <= '0';
      -- pragma translate_off
      if (RESET='0') then
      -- pragma translate_on
      if ( cnt_read_address = reg_write_address ) then
         cmp_empty <= '1';
      end if;
      -- pragma translate_off
      end if;
      -- pragma translate_on
   end process;

   -- Comparator for FULL signal ----------------------------------------------
   cmp_fullp: process(reg_read_address, cnt_write_address)
   begin
      cmp_full <= '0';
      -- pragma translate_off
      if (RESET='0') then
      -- pragma translate_on
      if ((reg_read_address (ADDRESS_WIDTH-1 downto 0) =
          cnt_write_address(ADDRESS_WIDTH-1 downto 0) ) and
         (reg_read_address (ADDRESS_WIDTH) /=
          cnt_write_address(ADDRESS_WIDTH) )) then
         cmp_full <= '1';
      end if;
      -- pragma translate_off
      end if;
      -- pragma translate_on
   end process;

   -- Full and empty signals --------------------------------------------------
   sig_empty <= cmp_empty and sig_read_allowed and not sig_write_allowed;
   sig_full  <= cmp_full and not sig_read_allowed and sig_write_allowed;


   -- register reg_empty -----------------------------------------------------
   reg_emptyp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_empty <= '1';
      elsif (CLK'event AND CLK = '1') then
         if (sig_empty_full_we = '1') then
            reg_empty <= sig_empty;
         end if;
      end if;
   end process;

   -- register reg_full ------------------------------------------------------
   reg_fullp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_full <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (sig_empty_full_we = '1') then
            reg_full <= sig_full;
         end if;
      end if;
   end process;

   -- last block identification ----------------------------------------------
   LAST_BLOCK_DETECTION : if (BLOCK_SIZE > 0) generate

   process(cnt_diff, sig_read_allowed, sig_write_allowed)
   begin
     if (cnt_diff = BLOCK_SIZE) and (sig_read_allowed = '1') and
        (sig_write_allowed = '0') then
           lstblk_plus_one <= '1';
     else
           lstblk_plus_one <= '0';
     end if;
   end process;

   process(cnt_diff, sig_write_allowed, sig_read_allowed)
   begin
     if (cnt_diff = BLOCK_SIZE + 1 ) and (sig_write_allowed = '1') and
        (sig_read_allowed = '0') then
          lstblk_minus_one <= '1';
     else
          lstblk_minus_one <= '0';
     end if;
   end process;

   -- cnt_diff counter
   cnt_diff_ce <= sig_read_allowed xor sig_write_allowed;
   cnt_diff_dir <= sig_read_allowed;
   process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_diff <= conv_std_logic_vector(ITEMS, cnt_diff'length);
      elsif (CLK'event AND CLK = '1') then
         if (cnt_diff_ce = '1') then
            if (cnt_diff_dir = '1') then
               cnt_diff <= cnt_diff + 1;
            else
               cnt_diff <= cnt_diff - 1;
            end if;
         end if;
      end if;
   end process;

   -- reg_lstblk register and comparator
   process(RESET, CLK)
   begin
      if (RESET = '1') then
         if (BLOCK_SIZE < ITEMS) then
            reg_lstblk <= '0';
         else
            reg_lstblk <= '1';
         end if;
      elsif (CLK'event AND CLK = '1') then
         if (lstblk_plus_one = '1') or (lstblk_minus_one = '1') then
            reg_lstblk <= lstblk_minus_one and not lstblk_plus_one;
         end if;
      end if;
   end process;

   end generate;

   -- Output signals ----------------------------------------------------------
   FULL  <= reg_full;
   EMPTY <= reg_empty;
   LSTBLK <= reg_lstblk;

end architecture fifo_arch;
