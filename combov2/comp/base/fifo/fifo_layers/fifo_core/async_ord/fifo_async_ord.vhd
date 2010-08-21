--
-- fifo_async_ord.vhd: Asynchronous ordinary FIFO full architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
--            Martinek Tomas <martinek@liberouter.org>
--            Martin Mikusek <martin.mikusek@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Cache package
use work.fifo_pkg.all;

-- Math package - log2 function
use work.math_pack.all;

-- counter package
use work.cnt_types.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on



architecture full of fifo_async_ord is

   -- Number of address bits
   constant FADDR       : integer := log2(ITEMS)-1;

   -- Read part signals
   signal cnt_read_addr       : std_logic_vector(FADDR downto 0);
   signal read_addrgray       : std_logic_vector(FADDR downto 0);
   signal read_nextgray       : std_logic_vector(FADDR downto 0);
   signal read_lastgray       : std_logic_vector(FADDR downto 0);
 
   -- Write part signals
   signal cnt_write_addr      : std_logic_vector(FADDR downto 0);
   signal write_addrgray      : std_logic_vector(FADDR downto 0);
   signal write_nextgray      : std_logic_vector(FADDR downto 0);
 
   -- Status part signals
   signal reg_status          : std_logic_vector(FADDR downto 0);
   signal read_truegray       : std_logic_vector(FADDR downto 0);
   signal reg_read_truegray   : std_logic_vector(FADDR downto 0);
   signal read_bin            : std_logic_vector(FADDR downto 0);
   signal reg_cnt_write_addr  : std_logic_vector(FADDR downto 0);

   -- Allow signals
   signal read_allow          : std_logic;
   signal write_allow         : std_logic;
   signal empty_allow         : std_logic;
   signal full_allow          : std_logic;

   -- Fast carry logic signals
   signal ecomp               : std_logic_vector(FADDR downto 0);
   signal fcomp               : std_logic_vector(FADDR downto 0);
   signal emuxcyo             : std_logic_vector(FADDR+1 downto 0);
   signal fmuxcyo             : std_logic_vector(FADDR+1 downto 0);
   signal emptyg              : std_logic;
   signal fullg               : std_logic;
   signal regasync_full       : std_logic;
   signal regasync_empty      : std_logic;
   signal gnd                 : std_logic;
   signal pwr                 : std_logic;
  
   -- FIFO_MEM output signals
   signal mem_out             : std_logic_vector((ITEM_WIDTH - 1) downto 0);
   signal reg_mem_out         : std_logic_vector((ITEM_WIDTH - 1) downto 0);
   signal mem_data_valid      : std_logic;
   signal reg_mem_data_valid  : std_logic;

   -- FIFO_MEM input and help signals
   signal prefetch_allow        : std_logic;
   signal sig_prefetch       : std_logic;
   signal was_prefetch        : std_logic; -- help signal (prefetch mode only)
   signal mem_pipe_en         : std_logic;


   component MUXCY_L
      port (
         DI:  in std_logic;
         CI:  in std_logic;
         S:   in std_logic;
         LO: out std_logic
      );
   end component;
  

begin
   -- ------------------------------------------------------------------------
   --                       Memory Instantion
   -- ------------------------------------------------------------------------
   DO <= reg_mem_out;
   DO_DV <= reg_mem_data_valid;

   -- FIFO memory instance
   memory : entity work.FIFO_MEM
   generic map (
      MEM_TYPE => MEM_TYPE,
      LATENCY => LATENCY,
      ITEMS => ITEMS,
      ITEM_WIDTH => ITEM_WIDTH
   )
   port map (
      CLKW => WR_CLK,
      WRITE_EN => write_allow,
      WRITE_ADDR => cnt_write_addr,
      DI => DI,
      PIPE_EN => mem_pipe_en,

      CLKR => RD_CLK,
      READ_EN => sig_prefetch,
      RE_ADDR => cnt_read_addr,

      DO => mem_out,
      DO_DV => mem_data_valid,
      ADDR_OUT => open,

      RESET => RESET
   );


   -- -------------------------------------------------------------------------
   -- NON PREFETCH MODE
   -- -------------------------------------------------------------------------
   non_prefetch_fifo : if (PREFETCH = false) generate
      reg_mem_out <= mem_out;
      reg_mem_data_valid <= mem_data_valid;
      sig_prefetch <= read_allow;
      mem_pipe_en <= '1';
      was_prefetch <= 'Z';
   end generate;


   -- --------------------------------------------------------------------------
   -- PREFETCH MODE
   -- --------------------------------------------------------------------------
   prefetch_fifo : if (PREFETCH = true) generate
   
      sig_prefetch <= prefetch_allow and not regasync_empty;
      mem_pipe_en <= sig_prefetch or RD or not reg_mem_data_valid;

      process(RD_CLK)
      begin
         -- no need for RESET
         if (RD_CLK'event and RD_CLK = '1') then
            prefetch_allow <= read_allow or (not regasync_empty and not reg_mem_data_valid and not was_prefetch);
         end if;
      end process;

      process(RESET, RD_CLK)
      begin
         -- no need for RESET
         if (RD_CLK'event and RD_CLK = '1') then
            if ((sig_prefetch = '1' or was_prefetch = '1') and RD /= '1') then
               was_prefetch <= '1';
            else
               was_prefetch <= '0';
            end if;
         end if;
      end process;


      -- -----------------------------------------------------------------------
      -- Prefetch register
      -- -----------------------------------------------------------------------
      process(RESET, RD_CLK)
      begin
         if (RESET = '1') then
            reg_mem_out <= (others => '0');
         elsif (RD_CLK'event and RD_CLK = '1') then
            if (mem_pipe_en = '1') then
               reg_mem_out <= mem_out;
            end if;
         end if;
      end process;
    

      process(RESET, RD_CLK)
      begin
         if (RESET = '1') then
            reg_mem_data_valid <= '0';
         elsif (RD_CLK'event and RD_CLK = '1') then
            if (RD = '0' and (mem_data_valid = '1' or reg_mem_data_valid = '1')) then
               reg_mem_data_valid <= '1';
            else
               reg_mem_data_valid <= '0';
            end if;
         end if;
      end process;

   end generate;


   -- --------------------------------------------------------------------------
   --                       FIFO Control Part
   -- --------------------------------------------------------------------------
   
   --  allow flags generation
   read_allow <= (RD and not regasync_empty);
   write_allow <= (WR and not regasync_full);

   full_allow <= (regasync_full or WR);
   empty_allow <= (regasync_empty or RD);

   ---------------------------------------------------------------
   --  empty and full flag generation
   process (RD_CLK, RESET)
   begin
      if (RESET = '1') then
         regasync_empty <= '1';
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (empty_allow = '1') then
            regasync_empty <= emptyg;
         end if;
      end if;
   end process;

   process (WR_CLK, RESET)
   begin
     if (RESET = '1') then
        regasync_full <= '1';
     elsif (WR_CLK'event and WR_CLK = '1') then
        if (full_allow = '1') then
           regasync_full <= fullg;
        end if;
     end if;
   end process;

   ----------------------------------------------------------------
   --              Read Address Generation
   ----------------------------------------------------------------
   cnt_read_addr_up : entity work.cnt
   generic map(
      WIDTH => FADDR+1,
      DIR   => up,
      CLEAR => false
   )
   port map(
      RESET => RESET,
      CLK   => RD_CLK,
      DO    => cnt_read_addr,
      CLR   => '0',
      CE    => read_allow
   );


   process (RD_CLK, RESET)
   begin
      if (RESET = '1') then
         read_nextgray <= conv_std_logic_vector(2**(FADDR), FADDR+1);
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (read_allow = '1') then
            -- binary to gray convertor
            read_nextgray(FADDR) <= cnt_read_addr(FADDR);
            for i in FADDR-1 downto 0 loop
               read_nextgray(i) <= cnt_read_addr(i+1) xor cnt_read_addr(i);
            end loop;
         end if;
      end if;
   end process;

   process (RD_CLK, RESET)
   begin
     if (RESET = '1') then
        read_addrgray <= conv_std_logic_vector(2**(FADDR)+1, FADDR+1);
     elsif (RD_CLK'event and RD_CLK = '1') then
        if (read_allow = '1') then
           read_addrgray <= read_nextgray;
        end if;
     end if;
   end process;

   proc6: process (RD_CLK, RESET)
   begin
      if (RESET = '1') then
         read_lastgray <= conv_std_logic_vector(2**(FADDR)+3, FADDR+1);
      elsif (RD_CLK'event and RD_CLK = '1') then
         if (read_allow = '1') then
            read_lastgray <= read_addrgray;
         end if;
      end if;
   end process proc6;

   ----------------------------------------------------------------
   --             Write Address Genearation
   ----------------------------------------------------------------
   cnt_write_addr_u : entity work.cnt
   generic map(
      WIDTH => FADDR+1,
      DIR   => up,
      CLEAR => false
   )
   port map(
      RESET => RESET,
      CLK   => WR_CLK,
      DO    => cnt_write_addr,
      CLR   => '0',
      CE    => write_allow
   );


   process (WR_CLK, RESET)
   begin
     if (RESET = '1') then
        write_nextgray <= conv_std_logic_vector(2**(FADDR), FADDR+1);
     elsif (WR_CLK'event and WR_CLK = '1') then
         if (write_allow = '1') then
            -- binary to gray convertor
            write_nextgray(FADDR) <= cnt_write_addr(FADDR);
            for i in FADDR-1 downto 0 loop
               write_nextgray(i) <= cnt_write_addr(i+1) xor cnt_write_addr(i);
            end loop;
         end if;
      end if;
   end process;

   process (WR_CLK, RESET)
   begin
      if (RESET = '1') then
         write_addrgray <= conv_std_logic_vector(2**(FADDR)+1, FADDR+1);
      elsif (WR_CLK'event and WR_CLK = '1') then
         if (write_allow = '1') then
            write_addrgray <= write_nextgray;
         end if;
      end if;
   end process;

   ----------------------------------------------------------------
   --                     Fast carry logic
   ----------------------------------------------------------------
   gnd      <= '0';
   pwr      <= '1';
   
   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   ECOMP_GEN : for i in 0 to FADDR generate
      ecomp(i) <= (not (write_addrgray(i) xor read_addrgray(i)) and regasync_empty) or
                  (not (write_addrgray(i) xor read_nextgray(i)) and not regasync_empty);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   emuxcyo(0)  <= pwr;
   emptyg      <= emuxcyo(FADDR+1);
 
   EMUXCY_GEN : for i in 0 to FADDR generate
      emuxcyX: MUXCY_L
      port map (
         DI => gnd,
         CI => emuxcyo(i),
         S  => ecomp(i),
         LO => emuxcyo(i+1)
      );
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   FCOMP_GEN : for i in 0 to FADDR generate
      fcomp(i) <= (not (read_lastgray(i) xor write_addrgray(i)) and regasync_full) or
                  (not (read_lastgray(i) xor write_nextgray(i)) and not regasync_full);
   end generate;

   -- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   fmuxcyo(0)  <= pwr;
   fullg       <= fmuxcyo(FADDR+1);

   FMUXCY_GEN : for i in 0 to FADDR generate
      fmuxcyX: MUXCY_L
      port map (
         DI => gnd,
         CI => fmuxcyo(i),
         S  => fcomp(i),
         LO => fmuxcyo(i+1)
      );
   end generate;

   ----------------------------------------------------------------
   --             Status Genearation
   ----------------------------------------------------------------
   -- graycode read address generation
   read_truegray_p: process (RD_CLK, RESET)
   begin
      if (RESET='1') then
         read_truegray <= (others=>'0');
      elsif (RD_CLK'event and RD_CLK='1') then
         ----------------------------------------------------
         read_truegray(FADDR) <= cnt_read_addr(FADDR);
         read_truegray_gen : for i in FADDR-1 downto 0 loop
            read_truegray(i) <= cnt_read_addr(i+1) xor cnt_read_addr(i);
         end loop;
      end if;
   end process;

   -- synchronization with WR_CLK
   reg_read_truegray_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_read_truegray <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         reg_read_truegray <= read_truegray;
      end if;
   end process;

   -- transformation to binary format
   read_bin(FADDR) <= reg_read_truegray(FADDR);
   read_bin_gen : for i in FADDR-1 downto 0 generate
      read_bin(i) <= read_bin(i+1) xor reg_read_truegray(i);
   end generate;

   -- registering of cnt_write_addr
   reg_cnt_write_addr_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_cnt_write_addr <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         reg_cnt_write_addr <= cnt_write_addr;
      end if;
   end process;

   -- status computing
   reg_status_p: process (WR_CLK, RESET)
   begin
      if (RESET='1') then
         reg_status <= (others=>'0');
      elsif (WR_CLK'event and WR_CLK='1') then
         reg_status <= (reg_cnt_write_addr - read_bin);
      end if;
   end process;

   ----------------------------------------------------------------
   --                   Interface Mapping
   ----------------------------------------------------------------
   FULL     <= regasync_full;
   EMPTY    <= regasync_empty;
   STATUS <= reg_status;


end architecture full;
