-- hgen_new.vhd: New 10G Hash Generator 
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Architecture: new
-- ----------------------------------------------------------------------------
architecture new_arch of HGEN is
   signal fl_fork_in_sof_n              : std_logic;
   signal fl_fork_in_sop_n              : std_logic;
   signal fl_fork_in_eop_n              : std_logic;
   signal fl_fork_in_eof_n              : std_logic;
   signal fl_fork_in_src_rdy_n          : std_logic;
   signal fl_fork_in_dst_rdy_n          : std_logic;
   signal fl_fork_in_data               : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_fork_in_rem                : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_mask_in_sof_n              : std_logic;
   signal fl_mask_in_sop_n              : std_logic;
   signal fl_mask_in_eop_n              : std_logic;
   signal fl_mask_in_eof_n              : std_logic;
   signal fl_mask_in_src_rdy_n          : std_logic;
   signal fl_mask_in_dst_rdy_n          : std_logic;
   signal fl_mask_in_data               : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_mask_in_rem                : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_mask_out_sof_n             : std_logic;
   signal fl_mask_out_sop_n             : std_logic;
   signal fl_mask_out_eop_n             : std_logic;
   signal fl_mask_out_eof_n             : std_logic;
   signal fl_mask_out_src_rdy_n         : std_logic;
   signal fl_mask_out_dst_rdy_n         : std_logic;
   signal fl_mask_out_data              : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_mask_out_rem               : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);

   signal fl_fifo_in_sof_n              : std_logic;
   signal fl_fifo_in_sop_n              : std_logic;
   signal fl_fifo_in_eop_n              : std_logic;
   signal fl_fifo_in_eof_n              : std_logic;
   signal fl_fifo_in_src_rdy_n          : std_logic;
   signal fl_fifo_in_dst_rdy_n          : std_logic;
   signal fl_fifo_in_data               : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_fifo_in_rem                : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_conv_in_sof_n              : std_logic;
   signal fl_conv_in_sop_n              : std_logic;
   signal fl_conv_in_eop_n              : std_logic;
   signal fl_conv_in_eof_n              : std_logic;
   signal fl_conv_in_src_rdy_n          : std_logic;
   signal fl_conv_in_dst_rdy_n          : std_logic;
   signal fl_conv_in_data               : std_logic_vector(127 downto 0);
   signal fl_conv_in_rem                : std_logic_vector(log2(128 / 8 ) - 1 downto 0);
   
   signal fl_fifo_out_sof_n             : std_logic;
   signal fl_fifo_out_sop_n             : std_logic;
   signal fl_fifo_out_eop_n             : std_logic;
   signal fl_fifo_out_eof_n             : std_logic;
   signal fl_fifo_out_src_rdy_n         : std_logic;
   signal fl_fifo_out_dst_rdy_n         : std_logic;
   signal fl_fifo_out_data              : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_fifo_out_rem               : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_mark_fsm_out_src_rdy_n     : std_logic;
   signal fl_mark_fsm_out_dst_rdy_n     : std_logic;
   
   signal fl_marker_out_sof_n           : std_logic;
   signal fl_marker_out_sop_n           : std_logic;
   signal fl_marker_out_eop_n           : std_logic;
   signal fl_marker_out_eof_n           : std_logic;
   signal fl_marker_out_src_rdy_n       : std_logic;
   signal fl_marker_out_dst_rdy_n       : std_logic;
   signal fl_marker_out_data            : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_marker_out_rem             : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_pi_out_sof_n               : std_logic;
   signal fl_pi_out_sop_n               : std_logic;
   signal fl_pi_out_eop_n               : std_logic;
   signal fl_pi_out_eof_n               : std_logic;
   signal fl_pi_out_src_rdy_n           : std_logic;
   signal fl_pi_out_dst_rdy_n           : std_logic;
   signal fl_pi_out_data                : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_pi_out_rem                 : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal fl_trim_out_sof_n             : std_logic;
   signal fl_trim_out_sop_n             : std_logic;
   signal fl_trim_out_eop_n             : std_logic;
   signal fl_trim_out_eof_n             : std_logic;
   signal fl_trim_out_src_rdy_n         : std_logic;
   signal fl_trim_out_dst_rdy_n         : std_logic;
   signal fl_trim_out_data              : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal fl_trim_out_rem               : std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
   
   signal data                          : std_logic_vector(95 downto 0);
   signal sof                           : std_logic;
   signal eof                           : std_logic;
   signal vld                           : std_logic;
   signal rdy                           : std_logic;
   
   signal reg_init                      : std_logic_vector(31 downto 0) := (others => '0');
   signal reg_init_we                   : std_logic;
   
   signal hash                          : std_logic_vector(95 downto 0);
   signal hash_mod                      : std_logic_vector(FLOWID_WIDTH - 1 downto 0);
   signal hash_vld                      : std_logic;
   signal hash_ack                      : std_logic;
   
begin

   -- check if max number of hashes in hash fifo is bigger than max number of UH in FL Fifo 
   assert (ITEMS * DATA_WIDTH / 8 / UH_SIZE < HASH_FIFO_ITEMS) report "HGEN: Condition ITEMS * DATA_WIDTH / 8 / UH_SIZE < HASH_FIFO_ITEMS failed!" severity failure;
   
   -- check if whole UH can be stored in input fifo
   assert ((UH_SIZE + 11) / 12 <= INPUT_FIFO_ITEMS) report "HGEN: Condition (UH_SIZE + 11) / 12 <= INPUT_FIFO_ITEMS failed!" severity failure;
   
   -- check if whole UH can be stored in FL FIFO
   assert ((UH_SIZE + DATA_WIDTH/8 - 1) / (DATA_WIDTH/8) <= ITEMS) report "HGEN: Condition (UH_SIZE + DATA_WIDTH/8 - 1) / (DATA_WIDTH/8) <= ITEMS failed!" severity failure;
   
   fl_fork_in_data      <= RX_DATA;      
   fl_fork_in_rem       <= RX_REM;        
   fl_fork_in_src_rdy_n <= RX_SRC_RDY_N;
   RX_DST_RDY_N         <= fl_fork_in_dst_rdy_n;
   fl_fork_in_sop_n     <= RX_SOP_N;       
   fl_fork_in_eop_n     <= RX_EOP_N;       
   fl_fork_in_sof_n     <= RX_SOF_N;       
   fl_fork_in_eof_n     <= RX_EOF_N;       
   
   -- send input framelink to 2 output interfaces
   FL_FORK1TO2_U: entity work.FL_FORK_1TO2
   generic map(
      -- Frame link width
      DATA_WIDTH  => DATA_WIDTH
      )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      
      -- Input Interface
      RX_DATA        => fl_fork_in_data,
      RX_REM         => fl_fork_in_rem,
      RX_SRC_RDY_N   => fl_fork_in_src_rdy_n,
      RX_DST_RDY_N   => fl_fork_in_dst_rdy_n,
      RX_SOP_N       => fl_fork_in_sop_n,
      RX_EOP_N       => fl_fork_in_eop_n,
      RX_SOF_N       => fl_fork_in_sof_n,
      RX_EOF_N       => fl_fork_in_eof_n,

      -- Output Interfaces
      TX0_DATA       => fl_fifo_in_data,
      TX0_REM        => fl_fifo_in_rem,
      TX0_SRC_RDY_N  => fl_fifo_in_src_rdy_n,
      TX0_DST_RDY_N  => fl_fifo_in_dst_rdy_n,
      TX0_SOP_N      => fl_fifo_in_sop_n,
      TX0_EOP_N      => fl_fifo_in_eop_n,
      TX0_SOF_N      => fl_fifo_in_sof_n,
      TX0_EOF_N      => fl_fifo_in_eof_n,
                        
      TX1_DATA       => fl_mask_in_data,
      TX1_REM        => fl_mask_in_rem,
      TX1_SRC_RDY_N  => fl_mask_in_src_rdy_n,
      TX1_DST_RDY_N  => fl_mask_in_dst_rdy_n,
      TX1_SOP_N      => fl_mask_in_sop_n,
      TX1_EOP_N      => fl_mask_in_eop_n,
      TX1_SOF_N      => fl_mask_in_sof_n,
      TX1_EOF_N      => fl_mask_in_eof_n
   );
   
   -- This fifo store input UH
   -- Size of this fifo have to be less than 32 UH
   FL_FIFO_U: entity work.FL_FIFO
   generic map(
      -- Data width
      -- Should be multiple of 16: only 16,32,64,128 supported
      DATA_WIDTH     => DATA_WIDTH,
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS      => USE_BRAMS_FOR_FIFO,
      -- number of items in the FIFO
      ITEMS          => ITEMS,
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     => 1,
      -- Width of STATUS signal available
      STATUS_WIDTH   => 1,
      -- Number of parts in each frame
      PARTS          => 1
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
   
      -- write interface
      RX_DATA        => fl_fifo_in_data,
      RX_REM         => fl_fifo_in_rem,
      RX_SRC_RDY_N   => fl_fifo_in_src_rdy_n,
      RX_DST_RDY_N   => fl_fifo_in_dst_rdy_n,
      RX_SOP_N       => fl_fifo_in_sop_n,
      RX_EOP_N       => fl_fifo_in_eop_n,
      RX_SOF_N       => fl_fifo_in_sof_n,
      RX_EOF_N       => fl_fifo_in_eof_n,
      
      -- read interface
      TX_DATA        => fl_fifo_out_data,
      TX_REM         => fl_fifo_out_rem,
      TX_SRC_RDY_N   => fl_fifo_out_src_rdy_n,
      TX_DST_RDY_N   => fl_fifo_out_dst_rdy_n,
      TX_SOP_N       => fl_fifo_out_sop_n,
      TX_EOP_N       => fl_fifo_out_eop_n,
      TX_SOF_N       => fl_fifo_out_sof_n,
      TX_EOF_N       => fl_fifo_out_eof_n,

      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );

   -- Mask UH for hash computation
   MASK_U: entity work.MASK
   generic map(
      -- the data width of the data input/output
      DATA_WIDTH     => DATA_WIDTH,
      -- defines UH size in bytes; min 16 - 128 bytes
      UH_SIZE        => UH_SIZE
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,
      
      -- RX Framelink interface
      RX_DATA           => fl_mask_in_data,
      RX_REM            => fl_mask_in_rem,
      RX_SRC_RDY_N      => fl_mask_in_src_rdy_n,
      RX_DST_RDY_N      => fl_mask_in_dst_rdy_n,
      RX_SOP_N          => fl_mask_in_sop_n,
      RX_EOP_N          => fl_mask_in_eop_n,
      RX_SOF_N          => fl_mask_in_sof_n,
      RX_EOF_N          => fl_mask_in_eof_n,
   

      -- TX FrameLink interface
      TX_DATA           => fl_mask_out_data,
      TX_REM            => fl_mask_out_rem,
      TX_SRC_RDY_N      => fl_mask_out_src_rdy_n,
      TX_DST_RDY_N      => fl_mask_out_dst_rdy_n,
      TX_SOP_N          => fl_mask_out_sop_n,
      TX_EOP_N          => fl_mask_out_eop_n,
      TX_SOF_N          => fl_mask_out_sof_n,
      TX_EOF_N          => fl_mask_out_eof_n,
      
      -- Masking input, typically constant
      MASK              => MASK
   ); 
   
   -- HGEN runs internaly on 128/96 bit - so if DataWidth is different
   -- transformer is needed
   gen_link: if (DATA_WIDTH = 128) generate
      fl_conv_in_sof_n         <= fl_mask_out_sof_n;     
      fl_conv_in_sop_n         <= fl_mask_out_sop_n;     
      fl_conv_in_eop_n         <= fl_mask_out_eop_n;     
      fl_conv_in_eof_n         <= fl_mask_out_eof_n;     
      fl_conv_in_src_rdy_n     <= fl_mask_out_src_rdy_n; 
      fl_mask_out_dst_rdy_n    <= fl_conv_in_dst_rdy_n;
      fl_conv_in_data          <= fl_mask_out_data;      
      fl_conv_in_rem           <= fl_mask_out_rem;       
   end generate;               
   
   gen_trans: if (not(DATA_WIDTH = 128)) generate
      TRANSFORMER_U: entity work.fl_transformer
      generic map(
         RX_DATA_WIDTH  => DATA_WIDTH,
         TX_DATA_WIDTH  => 128
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         --
         RX_DATA        => fl_mask_out_data,
         RX_REM         => fl_mask_out_rem,
         RX_SOF_N       => fl_mask_out_sof_n,
         RX_EOF_N       => fl_mask_out_eof_n,
         RX_SOP_N       => fl_mask_out_sop_n,
         RX_EOP_N       => fl_mask_out_eop_n,
         RX_SRC_RDY_N   => fl_mask_out_src_rdy_n,
         RX_DST_RDY_N   => fl_mask_out_dst_rdy_n,
         --
         TX_DATA        => fl_conv_in_data,
         TX_REM         => fl_conv_in_rem,
         TX_SOF_N       => fl_conv_in_sof_n,
         TX_EOF_N       => fl_conv_in_eof_n,
         TX_SOP_N       => fl_conv_in_sop_n,
         TX_EOP_N       => fl_conv_in_eop_n,
         TX_SRC_RDY_N   => fl_conv_in_src_rdy_n,
         TX_DST_RDY_N   => fl_conv_in_dst_rdy_n
      );
   end generate;

   -- convert from 128 bit FL to 96 bit internal data format (FL in positive
   -- logic without SOP, EOP and REM)
   CONV_U: entity work.CONV_128_TO_96
   port map(
      -- common signals
      -- global FGPA clock
      CLK            => CLK,
      
      -- global synchronous reset
      RESET          => RESET,
      
      -- RX Framelink interface
      RX_DATA        => fl_conv_in_data,
      RX_REM         => fl_conv_in_rem,
      RX_SOF_N       => fl_conv_in_sof_n,
      RX_EOF_N       => fl_conv_in_eof_n,
      RX_SOP_N       => fl_conv_in_sop_n,
      RX_EOP_N       => fl_conv_in_eop_n,
      RX_SRC_RDY_N   => fl_conv_in_src_rdy_n,
      RX_DST_RDY_N   => fl_conv_in_dst_rdy_n,
      
      -- Fifo interface
      DATA           => data,
      SOF            => sof,
      EOF            => eof,
      VLD            => vld,
      RDY            => rdy
   ); 

   -- Hash generator core      
   HGEN_CORE_U: entity work.HGEN_CORE
   generic map(
      UH_SIZE               => UH_SIZE,
      INPUT_FIFO_ITEMS      => INPUT_FIFO_ITEMS,
      HASH_FIFO_ITEMS       => HASH_FIFO_ITEMS,
      USE_BRAMS_FOR_MEMORY  => USE_BRAMS_FOR_MEMORY
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK           => CLK,

      -- global synchronous reset
      RESET         => RESET,
     
      -- RX 96-bit interface
      DATA          => data,
      SOF           => sof,
      EOF           => eof,
      VLD           => vld,
      RDY           => rdy,

      -- Hash initialisation vector
      INIT          => reg_init,
      
      -- Hash interface interface
      HASH          => hash,
      HASH_VLD      => hash_vld,
      HASH_ACK      => hash_ack
   );
   
   -- convert 96 bit hash to flow_id width
   gen_map_less: if (FLOWID_WIDTH <= 96) generate
      hash_mod <= hash(FLOWID_WIDTH - 1 downto 0);
   end generate;
    
   gen_map_more: if (FLOWID_WIDTH > 96) generate
      hash_mod <= conv_std_logic_vector(0, FLOWID_WIDTH - 96) & hash;
   end generate;
   
   -- register for BJH seed   
   init_reg: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_init <= (others => '1');
         else
            if reg_init_we = '1' then
               reg_init <= MI_DWR;
            end if;
         end if;
      end if;
   end process init_reg;
   
   -- address decoder for MI32 interface
   addr_dec: process(MI_WR, MI_ADDR)
   begin
      reg_init_we <= '0';
      if (MI_WR = '1') then
         if (conv_integer(MI_ADDR) = 0) then
            reg_init_we <= '1';
         end if;
      end if;
   end process addr_dec;
   
   MI_ARDY <= MI_RD or MI_WR;
   MI_DRDY <= MI_RD; -- Although it seems that nothing can be read
      
   -- FL MARKER
   marker_u: entity work.SIMPLE_FL_MARKER
   generic map(
      -- Frame link width
      DATA_WIDTH   => DATA_WIDTH,
      -- Header / Footer data present
      PARTS        => 1,
      -- Add "mark" to header
      MARK_PART    => 0,
      -- Mark options
      OFFSET       => 0, -- "Mark" position in FL Header in Bytes
      MARK_SIZE    => FLOWID_WIDTH / 8, -- Size of "Mark" in Bytes
      -- architecture switch (false = ReWrite, true = Insert)
      INSERT       => true

   )
   port map(
      CLK          => CLK,
      RST          => RESET,

      MARK         => hash_mod,
      MARK_VALID   => hash_vld,
      MARK_NEXT    => hash_ack,

      -- Write interface
      RX_DATA      => fl_fifo_out_data,
      RX_REM       => fl_fifo_out_rem,
      RX_SRC_RDY_N => fl_fifo_out_src_rdy_n,
      RX_DST_RDY_N => fl_fifo_out_dst_rdy_n,
      RX_SOP_N     => fl_fifo_out_sop_n,
      RX_EOP_N     => fl_fifo_out_eop_n,
      RX_SOF_N     => fl_fifo_out_sof_n,
      RX_EOF_N     => fl_fifo_out_eof_n,
                   
      -- Read interface
      TX_DATA      => fl_marker_out_data,
      TX_REM       => fl_marker_out_rem,
      TX_SRC_RDY_N => fl_marker_out_src_rdy_n,
      TX_DST_RDY_N => fl_marker_out_dst_rdy_n,
      TX_SOP_N     => fl_marker_out_sop_n,
      TX_EOP_N     => fl_marker_out_eop_n,
      TX_SOF_N     => fl_marker_out_sof_n,
      TX_EOF_N     => fl_marker_out_eof_n
   );

   TX_SOF_N                <= fl_marker_out_sof_n;
   TX_SOP_N                <= fl_marker_out_sop_n;
   TX_EOP_N                <= fl_marker_out_eop_n;
   TX_EOF_N                <= fl_marker_out_eof_n;
   TX_SRC_RDY_N            <= fl_marker_out_src_rdy_n;
   fl_marker_out_dst_rdy_n <= TX_DST_RDY_N;
   TX_DATA                 <= fl_marker_out_data;
   TX_REM                  <= fl_marker_out_rem;
                     
end architecture new_arch;
                                                                                                   
