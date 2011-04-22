-- hgen_core.vhd: Hash Generator Core 
-- Copyright (C) 2009 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: HGEN_CORE
-- ----------------------------------------------------------------------------
entity HGEN_CORE is
   generic(
      -- size of UH
      UH_SIZE          : integer := 64;
      -- items in input fifos
      INPUT_FIFO_ITEMS : integer := 16;
      -- items in hash fifo
      HASH_FIFO_ITEMS  : integer := 32
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK           : in std_logic;

      -- global synchronous reset
      RESET         : in std_logic;
     
      -- RX 96-bit interface
      DATA          : in  std_logic_vector(95 downto 0);
      SOF           : in  std_logic;
      EOF           : in  std_logic;
      VLD           : in  std_logic;
      RDY           : out std_logic;

      -- Hash initialisation vector
      INIT          : in std_logic_vector(31 downto 0);
      
      -- Hash interface interface
      HASH          : out std_logic_vector(95 downto 0);
      HASH_VLD      : out std_logic;
      HASH_ACK      : in  std_logic
   );
end entity HGEN_CORE;

-- ----------------------------------------------------------------------------
--  Architecture: HGEN_CORE
-- ----------------------------------------------------------------------------
architecture full of HGEN_CORE is
   -- number of pipeline stages in jenkins block
   constant INTERFACES : integer := 4;
   -- fifo latency - for LUT memory 1 
   constant LATENCY : integer := 1;
   -- all fifos in hgen_core use prefetch
   constant PREFETCH : boolean := true;
   -- all fifos in hgen_core uses memory composed of LUT
   constant MEMORY_TYPE : mem_type := BRAM;
   
   -- input fifos data width
   constant INPUT_FIFO_WIDTH : integer := 98;
   -- input fifos block type
   constant INPUT_BLOCK_TYPE: block_type := variable_size;
   -- block size - doesn't metter because variable_size is used
   constant INPUT_BLOCK_SIZE : integer := 6;
   -- input fifos don't use dicard
   constant INPUT_FIFO_DISCARD : discard_type := WriteDiscard;
   
   -- hash width
   constant HASH_FIFO_WIDTH : integer := 96;
   
   
   signal spliter_out_data : std_logic_vector((INTERFACES * 96) - 1 downto 0);
   signal spliter_out_sof  : std_logic_vector(INTERFACES - 1 downto 0);
   signal spliter_out_eof  : std_logic_vector(INTERFACES - 1 downto 0);
   signal spliter_out_vld  : std_logic_vector(INTERFACES - 1 downto 0);
   signal spliter_out_rdy  : std_logic_vector(INTERFACES - 1 downto 0);
   
   signal fifo_out_data    : std_logic_vector((INTERFACES * 96) - 1 downto 0);
   signal fifo_out_sof     : std_logic_vector(INTERFACES - 1 downto 0);
   signal fifo_out_eof     : std_logic_vector(INTERFACES - 1 downto 0);
   signal fifo_out_vld     : std_logic_vector(INTERFACES - 1 downto 0);
   signal fifo_out_rdy     : std_logic_vector(INTERFACES - 1 downto 0);
   signal fifo_out_blk_rdy : std_logic_vector(INTERFACES - 1 downto 0);
   
   signal fifo_mux_data    : std_logic_vector(95 downto 0);
   signal fifo_mux_sof     : std_logic;
   signal fifo_mux_eof     : std_logic;
   signal fifo_mux_vld     : std_logic;
   signal fifo_mux_rdy     : std_logic;
   signal fifo_mux_blk_rdy : std_logic;
   
   signal fifo_mux_sof_v      : std_logic_vector(0 downto 0);
   signal fifo_mux_eof_v      : std_logic_vector(0 downto 0);
   signal fifo_mux_vld_v      : std_logic_vector(0 downto 0);
   signal fifo_mux_rdy_v      : std_logic_vector(0 downto 0);
   signal fifo_mux_blk_rdy_v  : std_logic_vector(0 downto 0);
   
   signal jenkins_out_data : std_logic_vector(95 downto 0);
   signal jenkins_out_sof  : std_logic;
   signal jenkins_out_eof  : std_logic;
   signal jenkins_out_vld  : std_logic;
   signal jenkins_out_rdy  : std_logic;

   signal jenkins_in_vld   : std_logic;
   signal jenkins_in_rdy   : std_logic;
   
   signal full             : std_logic_vector(INTERFACES - 1 downto 0);
   signal wr               : std_logic_vector(INTERFACES - 1 downto 0);
   
   signal di               : std_logic_vector((INTERFACES * 98) - 1 downto 0);
   signal do               : std_logic_vector((INTERFACES * 98) - 1 downto 0);
   
   signal cnt_interfaces   : std_logic_vector(log2(INTERFACES) - 1 downto 0);
   
   signal hash_full        : std_logic;
   signal hash_empty       : std_logic;
   signal hash_dodv        : std_logic;
   signal hash_wr          : std_logic;
   signal hash_full_n      : std_logic;
   
   signal context_in             : std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal context_out            : std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal context_out_orig       : std_logic_vector((log2(INTERFACES) + 2) - 1 downto 0);
   signal context_in_vld         : std_logic;
   signal context_in_rdy         : std_logic;
   signal context_out_vld        : std_logic;
   signal context_out_rdy        : std_logic;
   signal context_out_vld_orig   : std_logic;
   
   signal input_type                : std_logic;
   signal rdy_out_intermediate      : std_logic;
   signal vld_in_start              : std_logic;
   signal vld_in_intermediate       : std_logic;
   signal rdy_out_end               : std_logic;
   signal fifo_mux_intermediate     : std_logic;
   signal context_data_vld          : std_logic;
   signal out_mux_sel               : std_logic;
   signal context_in_intermediate   : std_logic;
   signal context_out_intermediate  : std_logic;
   
   signal cnt_init_ce            : std_logic;
   signal cnt_init_count         : std_logic_vector(4 downto 0);
begin

   -- split input UHs to generic number of fifos 
   SPLITER_U: entity work.SPLITER
   generic map(
      -- number of output interfaces
      INTERFACES     => INTERFACES
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,
      
      -- RX 96-bit interface
      RX_DATA           => DATA,
      RX_SOF            => SOF,
      RX_EOF            => EOF,
      RX_VLD            => VLD,
      RX_RDY            => RDY,
   
      -- TX 96-bit interfaces
      TX_DATA           => spliter_out_data,
      TX_SOF            => spliter_out_sof, 
      TX_EOF            => spliter_out_eof, 
      TX_VLD            => spliter_out_vld, 
      TX_RDY            => spliter_out_rdy 
   );
   
   -- Generic number of fifos for storing input UH
   -- UH is processed by jenkins block only when whole UH is in fifo
   gen_fifo: for i in 0 to INTERFACES - 1 generate
   
      fifo_u : entity work.FIFO_SYNC_BLOCK
      generic map(
         MAIN_MEM   => MEMORY_TYPE,
         ADDR_MEM   => MEMORY_TYPE,
         LATENCY    => LATENCY,
         ITEMS      => INPUT_FIFO_ITEMS,
         ITEM_WIDTH => INPUT_FIFO_WIDTH,
         BLOCK_TYPE => INPUT_BLOCK_TYPE,
         BLOCK_SIZE => INPUT_BLOCK_SIZE,
         MAX_BLOCKS => INPUT_FIFO_ITEMS,
         DISCARD    => INPUT_FIFO_DISCARD,
         PREFETCH   => PREFETCH
      )
      port map(
         CLK        => CLK,
         RESET      => RESET,

         -- Write interface
         WR         => wr(i),
         DI         => di((i + 1) * 98 - 1 downto i * 98),
         BLK_END    => spliter_out_eof(i),
         WR_DISCARD => '0',

         -- Read interface
         RD         => fifo_out_rdy(i),
         DO         => do((i + 1) * 98 - 1 downto i * 98),
         DO_DV      => fifo_out_vld(i),
         BLK_READY  => open,--fifo_out_blk_rdy(i),
         BLK_FINISH => open,
         RD_DISCARD => '0',

         -- Info
         FULL       => full(i),
         EMPTY      => open,
         STATUS     => open
      );
      
      fifo_out_blk_rdy(i) <= fifo_out_vld(i);
      spliter_out_rdy(i) <= not full(i);
      wr(i) <= (not full(i)) and spliter_out_vld(i);
      di((i + 1) * 98 - 1 downto i * 98) <= spliter_out_data((i + 1) * 96 - 1 downto i * 96) & spliter_out_sof(i) & spliter_out_eof(i); 
      
      fifo_out_data((i + 1) * 96 - 1 downto i * 96) <= do((i + 1) * 98 - 1 downto i * 98 + 2);
      fifo_out_sof(i) <= do(i * 98 + 1);
      fifo_out_eof(i) <= do(i * 98);
      
   end generate gen_fifo;

   -- Generic muxs/demux for selection of input UH from fifos
   gen_mux_data: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 96,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => fifo_out_data,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_mux_data
   );
   
   gen_mux_sof: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => fifo_out_sof,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_mux_sof_v
   );
   
   gen_mux_eof: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => fifo_out_eof,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_mux_eof_v
   );
   
   gen_mux_vld: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => fifo_out_vld,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_mux_vld_v
   );
   
   gen_mux_blk: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 1,
      MUX_WIDTH   => INTERFACES
   )
   port map(
      DATA_IN     => fifo_out_blk_rdy,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_mux_blk_rdy_v
   );
   
   gen_demux_rdy: entity work.GEN_DEMUX
   generic map(
      DATA_WIDTH  => 1,
      DEMUX_WIDTH => INTERFACES,
      DEF_VALUE   => '0'
   )
   port map(
      DATA_IN     => fifo_mux_rdy_v,
      SEL         => cnt_interfaces,
      DATA_OUT    => fifo_out_rdy
   );
   
   fifo_mux_sof      <= fifo_mux_sof_v(0);
   fifo_mux_eof      <= fifo_mux_eof_v(0);
   fifo_mux_vld      <= fifo_mux_vld_v(0);
   fifo_mux_blk_rdy  <= fifo_mux_blk_rdy_v(0);
   fifo_mux_rdy_v(0) <= fifo_mux_rdy;
     

   -- control signals for jenkins block
   input_type              <= not fifo_mux_sof;
   hash_full_n             <= not hash_full;  -- just to look nice - never happen
   jenkins_in_vld          <= fifo_mux_vld and fifo_mux_blk_rdy;
   fifo_mux_rdy            <= fifo_mux_vld and fifo_mux_blk_rdy and context_in_rdy;
   context_in_vld          <= '1';
   hash_wr                 <= jenkins_out_vld and jenkins_out_sof and jenkins_out_eof and hash_full_n;
   jenkins_out_rdy         <= hash_full_n when jenkins_out_eof = '1' else jenkins_in_vld;
   context_data_vld        <= fifo_mux_vld and fifo_mux_blk_rdy;
   context_out_rdy         <= '1'; 
   
   -- context input data
   context_in(log2(INTERFACES) - 1 downto 0) <= context_out(log2(INTERFACES) - 1 downto 0);
   context_in(log2(INTERFACES))              <= context_data_vld;
   context_in(log2(INTERFACES) + 1)          <= fifo_mux_eof;

   -- Bob Jenkins Hash block
   JENKINS_U: entity work.jenkins
   generic map(
      INTERFACES     => INTERFACES,
      UH_SIZE        => UH_SIZE
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,

      DATA_IN           => fifo_mux_data,
      STATE             => jenkins_out_data,
      DATA_IN_VLD       => jenkins_in_vld,
      DATA_IN_NEXT      => jenkins_in_rdy,
      CONTEXT_IN_VLD    => context_in_vld,
      CONTEXT_IN_NEXT   => context_in_rdy,
      CONTEXT_IN        => context_in,
      INPUT_TYPE        => input_type,

      SEED              => INIT,

      DATA_OUT          => jenkins_out_data,
      CONTEXT_OUT       => context_out_orig,
      DATA_OUT_RDY      => jenkins_out_vld,
      DATA_OUT_NEXT     => jenkins_out_rdy,
      CONTEXT_OUT_RDY   => context_out_vld_orig,
      CONTEXT_OUT_NEXT  => context_out_rdy
   );
   
   -- context output data
   jenkins_out_eof <= context_out(log2(INTERFACES) + 1);
   jenkins_out_sof <= context_out(log2(INTERFACES));
   cnt_interfaces  <= context_out(log2(INTERFACES) - 1 downto 0);
   
   -- Next 3 processes are used for jenkins block initialisation
   -- first data can arive 4 CLK tick after reset
   cnt_init: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_init_count <= (others => '1');
         else
            if (cnt_init_ce = '1') then
               cnt_init_count <= cnt_init_count + '1';
            end if;
         end if;
      end if;
   end process cnt_init;
   
   ce_gen: process (cnt_init_count)
   begin
      if (cnt_init_count = conv_std_logic_vector(4,5)) then
         cnt_init_ce <= '0';
      else
         cnt_init_ce <= '1';
      end if;
   end process ce_gen;
     
   mux_cont: process (cnt_init_ce, context_out_vld_orig, RESET, cnt_init_count, context_out_orig)
   begin
     if (cnt_init_ce = '1' and RESET = '0') then
         context_out_vld <= '1';
         context_out     <= "00" & cnt_init_count(1 downto 0);
      else
         context_out_vld <= context_out_vld_orig;
         context_out     <= context_out_orig;
      end if;     
   end process mux_cont;
   
   -- output hash fifo - never will be full - UH fifo can store less UH than
   -- max. number UH hashes. This is necessery for easy control of jenkins
   -- block and to avoid logical loops
   hash_fifo_u: entity work.FIFO_SYNC_ORD
      generic map(
         MEM_TYPE   => MEMORY_TYPE,
         LATENCY    => LATENCY,
         ITEMS      => HASH_FIFO_ITEMS,
         ITEM_WIDTH => HASH_FIFO_WIDTH,
         PREFETCH   => PREFETCH
      )
      port map(
         CLK    => CLK,
         RESET  => RESET,
   
         WR     => hash_wr,
         DI     => jenkins_out_data,
   
         RD     => HASH_ACK,
         DO     => HASH,
         DO_DV  => HASH_VLD,
   
         FULL   => hash_full,
         EMPTY  => hash_empty,
         STATUS => open
      );
       
end architecture full;
