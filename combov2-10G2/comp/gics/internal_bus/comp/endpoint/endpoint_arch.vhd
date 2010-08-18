--
-- endpoint_arch.vhd : Internal Bus Endpoint architecture
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

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--           ARCHITECTURE DECLARATION  --  Internal Bus Endpoint             --
-- ----------------------------------------------------------------------------

architecture pipelined of IB_ENDPOINT is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------
   
   constant ZEROS : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   signal wr_data_in       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal wr_sof_n         : std_logic;
   signal wr_eof_n         : std_logic;
   signal wr_src_rdy_n     : std_logic;
   signal wr_dst_rdy_n     : std_logic;
   
   signal downrd_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal downrd_sof_n     : std_logic;
   signal downrd_eof_n     : std_logic;
   signal downrd_src_rdy_n : std_logic;
   signal downrd_dst_rdy_n : std_logic;

   signal cpl_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal cpl_sof_n        : std_logic;
   signal cpl_eof_n        : std_logic;
   signal cpl_src_rdy_n    : std_logic;
   signal cpl_dst_rdy_n    : std_logic;

   signal cpl_pipe_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal cpl_pipe_sof_n      : std_logic;
   signal cpl_pipe_eof_n      : std_logic;
   signal cpl_pipe_src_rdy_n  : std_logic;
   signal cpl_pipe_dst_rdy_n  : std_logic;
   
   signal rd_data_in       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rd_sof_n         : std_logic;
   signal rd_eof_n         : std_logic;
   signal rd_src_rdy_n     : std_logic;
   signal rd_dst_rdy_n     : std_logic;
   
   signal rd_pipe_data_in     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rd_pipe_sof_n       : std_logic;
   signal rd_pipe_eof_n       : std_logic;
   signal rd_pipe_src_rdy_n   : std_logic;
   signal rd_pipe_dst_rdy_n   : std_logic;

   signal up_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal up_sof_n         : std_logic;
   signal up_eof_n         : std_logic;
   signal up_src_rdy_n     : std_logic;
   signal up_dst_rdy_n     : std_logic;   

   signal rd_tag           : std_logic_vector(7 downto 0);
   signal rd_tag_vld       : std_logic;
   signal rd_done          : std_logic;
                                    
   signal cpl_tag          : std_logic_vector(7 downto 0);
   signal cpl_tag_vld      : std_logic;
   
   signal wr_en            : std_logic;
   signal wr_complete      : std_logic;
   signal rd_en            : std_logic;
   signal rd_complete      : std_logic;
   
   signal BM_SOF_N_aux     : std_logic;
   signal BM_SRC_RDY_N_aux : std_logic;
   signal BM_DST_RDY_N_aux : std_logic;
   signal bm_write         : std_logic;
   
begin
   
   -- Asserts -----------------------------------------------------------------
   assert DATA_WIDTH =  8 or DATA_WIDTH = 16 or DATA_WIDTH = 32 or
          DATA_WIDTH = 64 or DATA_WIDTH = 128
      report "DATA_WIDTH must be one of {8,16,32,64,128}."
      severity error;
   
   assert ADDR_WIDTH > 0
      report "ADDR_WIDTH must be at least 1."
      severity error;
   
   assert READ_IN_PROCESS > 0
      report "READ_IN_PROCESS must be at least 1."
      severity error;
   
   assert CONNECTED_TO = SWITCH_MASTER or 
          ENDPOINT_BASE + ENDPOINT_LIMIT > ENDPOINT_BASE
      report "Empty address space of endpoint. It can happen if " &
             "ENDPOINT_LIMIT is 0 or ENDPOINT_BASE + ENDPOINT_LIMIT is " &
             "greater than max 32bit value."
      severity warning;
   
   assert ADDR_WIDTH <= 32
      report "ADDR_WIDTH is not expected to be greater than 32."
      severity warning;
   
   assert CONNECTED_TO = SWITCH_MASTER or 
          ADDR_WIDTH >= log2(ENDPOINT_LIMIT)
      report "ADDR_WIDTH is set too low. Size of space addressable by ADDR " &
             "signals is smaller than space specified by ENDPOINT_LIMIT. " &
             "Set ADDR_WIDTH to log2(ENDPOINT_LIMIT)."
      severity warning;
   
   -- temp assert, 128bit is not working yet
   assert DATA_WIDTH < 128
      report "128 bit version of endpoint is not debugged yet."
      severity warning;
   
   -- -------------------------------------------------------------------------
   --                           DOWNSTREAM BUFFER                            --
   -- -------------------------------------------------------------------------

   U_down_buf : entity work.IB_ENDPOINT_DOWN_BUF
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH         => DATA_WIDTH,
      -- Endpoint Address Space 
      ENDPOINT_BASE      => ENDPOINT_BASE,
      ENDPOINT_LIMIT     => ENDPOINT_LIMIT,
      -- Endpoint is connected to
      CONNECTED_TO       => CONNECTED_TO,
      -- Input Buffer Size
      INPUT_BUFFER_SIZE  => INPUT_BUFFER_SIZE
   )
   port map (
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- IB Interface -------------------------------------
      IB_DATA      => IB_DOWN_DATA,     
      IB_SOF_N     => IB_DOWN_SOF_N,    
      IB_EOF_N     => IB_DOWN_EOF_N,    
      IB_SRC_RDY_N => IB_DOWN_SRC_RDY_N,
      IB_DST_RDY_N => IB_DOWN_DST_RDY_N,
                   
      -- WR Interface -------------------------------------
      WR_DATA      => wr_data_in,
      WR_SOF_N     => wr_sof_n,
      WR_EOF_N     => wr_eof_n,
      WR_SRC_RDY_N => wr_src_rdy_n,
      WR_DST_RDY_N => wr_dst_rdy_n,
                   
      -- RD Interface -------------------------------------
      RD_DATA      => downrd_data,
      RD_SOF_N     => downrd_sof_n,
      RD_EOF_N     => downrd_eof_n,
      RD_SRC_RDY_N => downrd_src_rdy_n,
      RD_DST_RDY_N => downrd_dst_rdy_n,
                   
     -- BM Done Interface ---------------------------------
      BM_TAG       => rd_tag,
      BM_TAG_VLD   => rd_tag_vld,
      BM_DONE      => rd_done
   );              
   
   -- -------------------------------------------------------------------------
   --                           STRICT ORDER UNIT                            --
   -- -------------------------------------------------------------------------
   
   strict_unit_gen_yes: if (STRICT_ORDER) generate
   
     U_strict_unit : entity work.IB_ENDPOINT_STRICT_UNIT
     port map (
        -- Common interface -----------------------------------------------------
      CLK           => CLK,
      RESET         => RESET,
      
      -- Write interface ------------------------------------------------------
      WR_SOF_N      => wr_sof_n,
      WR_SRC_RDY_N  => wr_src_rdy_n,
      WR_DST_RDY_N  => wr_dst_rdy_n,
      
      -- IB Read interface ----------------------------------------------------
      IB_SOF_N      => downrd_sof_n,
      IB_SRC_RDY_N  => downrd_src_rdy_n,
      IB_DST_RDY_N  => downrd_dst_rdy_n,
      
      -- BM Read interface ----------------------------------------------------
      BM_SOF_N      => BM_SOF_N_aux,
      BM_SRC_RDY_N  => BM_SRC_RDY_N_aux,
      BM_DST_RDY_N  => BM_DST_RDY_N_aux,
      BM_WRITE      => bm_write,
      
      -- Operation completion interface ---------------------------------------
      WR_COMPLETE   => wr_complete,
      RD_COMPLETE   => rd_complete,
      
      -- Output control interface ---------------------------------------------
      WR_EN         => wr_en,
      RD_EN         => rd_en
     );
   
   end generate;
   
   strict_unit_gen_no: if (not STRICT_ORDER) generate
     
     wr_en <= '1';
     rd_en <= '1';
     
   end generate;
   
   -- -------------------------------------------------------------------------
   --                            WRITE CONTROLLER                            --
   -- -------------------------------------------------------------------------

   U_write_ctrl : entity work.IB_ENDPOINT_WRITE_CTRL
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH   => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH   => ADDR_WIDTH
   ) 
   port map (
      -- Common interface ---------------------------------
      CLK          => CLK,
      RESET        => RESET,

      -- IB Interface -------------------------------------
      IB_DATA      => wr_data_in,
      IB_SOF_N     => wr_sof_n,
      IB_EOF_N     => wr_eof_n,
      IB_SRC_RDY_N => wr_src_rdy_n,
      IB_DST_RDY_N => wr_dst_rdy_n,

      -- Write Interface ----------------------------------
      WR_REQ       => WR_REQ,   
      WR_RDY       => WR_RDY,   
      WR_DATA      => WR_DATA,  
      WR_ADDR      => WR_ADDR,  
      WR_BE        => WR_BE,    
      WR_LENGTH    => WR_LENGTH,
      WR_SOF       => WR_SOF,   
      WR_EOF       => WR_EOF,   
      
      -- Strict unit interface ----------------------------
      WR_EN        => wr_en,
      WR_COMPLETE  => wr_complete
   );
   
   -- -------------------------------------------------------------------------
   --                            BUS MASTER UNIT                             --
   -- -------------------------------------------------------------------------

   -- without bus master functionality ----------------------------------------
   BM_UNIT_GEN_NO: if (not BUS_MASTER_ENABLE) generate

      rd_data_in         <= downrd_data;
      rd_sof_n           <= downrd_sof_n;
      rd_eof_n           <= downrd_eof_n;
      rd_src_rdy_n       <= downrd_src_rdy_n;
      downrd_dst_rdy_n   <= rd_dst_rdy_n;

      up_data            <= cpl_pipe_data;
      up_sof_n           <= cpl_pipe_sof_n;
      up_eof_n           <= cpl_pipe_eof_n;
      up_src_rdy_n       <= cpl_pipe_src_rdy_n;
      cpl_pipe_dst_rdy_n <= up_dst_rdy_n;   
      
      BM_SOF_N_aux       <= '1';
      BM_SRC_RDY_N_aux   <= '1';
      BM_DST_RDY_N_aux   <= '1';
      bm_write           <= '0';
      
   end generate;

   -- with bus master functionality -------------------------------------------   
   BM_UNIT_GEN_YES: if (BUS_MASTER_ENABLE) generate 
   
      U_bm_unit : entity work.IB_ENDPOINT_BM_UNIT
      generic map (
         DATA_WIDTH     => DATA_WIDTH
      )
      port map (
         -- Common interface ------------------------------
         CLK            => CLK,
         RESET          => RESET,
  
         -- Read interface --------------------------------
         RD_DATA        => downrd_data,
         RD_SOF_N       => downrd_sof_n,
         RD_EOF_N       => downrd_eof_n,
         RD_SRC_RDY_N   => downrd_src_rdy_n,
         RD_DST_RDY_N   => downrd_dst_rdy_n,

         -- Completion interface --------------------------
         CPL_DATA       => cpl_pipe_data,
         CPL_SOF_N      => cpl_pipe_sof_n,
         CPL_EOF_N      => cpl_pipe_eof_n,
         CPL_SRC_RDY_N  => cpl_pipe_src_rdy_n,
         CPL_DST_RDY_N  => cpl_pipe_dst_rdy_n,

         -- Bus Master interface --------------------------
         BM_DATA        => BM_DATA,     
         BM_SOF_N       => BM_SOF_N,    
         BM_EOF_N       => BM_EOF_N,    
         BM_SRC_RDY_N   => BM_SRC_RDY_N,
         BM_DST_RDY_N   => BM_DST_RDY_N_aux,
  
         -- DOWN multiplexed interface --------------------
         DOWN_DATA      => rd_data_in,
         DOWN_SOF_N     => rd_sof_n,
         DOWN_EOF_N     => rd_eof_n,
         DOWN_SRC_RDY_N => rd_src_rdy_n,
         DOWN_DST_RDY_N => rd_dst_rdy_n,

         -- UP multiplexed interface ----------------------
         UP_DATA        => up_data,
         UP_SOF_N       => up_sof_n,
         UP_EOF_N       => up_eof_n,
         UP_SRC_RDY_N   => up_src_rdy_n,
         UP_DST_RDY_N   => up_dst_rdy_n,

         -- G2LR DONE interface ---------------------------
         RD_TAG         => rd_tag,
         RD_TAG_VLD     => rd_tag_vld,
         RD_DONE        => rd_done,
                        
         -- L2GW DONE interface ---------------------------
         CPL_TAG        => cpl_tag,
         CPL_TAG_VLD    => cpl_tag_vld,
                        
         -- BM DONE interface -----------------------------
         BM_TAG         => BM_TAG,
         BM_TAG_VLD     => BM_TAG_VLD
      );
      
      BM_SOF_N_aux     <= BM_SOF_N;
      BM_SRC_RDY_N_aux <= BM_SRC_RDY_N;
      BM_DST_RDY_N     <= BM_DST_RDY_N_aux;
      bm_write         <= BM_DATA(C_IB_TYPE_DATA);
      
   end generate;
   
   -- -------------------------------------------------------------------------
   --                        PIPE TO READ CONTROLLER                         --
   -- -------------------------------------------------------------------------
   
   U_rd_pipe: entity work.IB_PIPE
   generic map (
      DATA_WIDTH      => DATA_WIDTH,
      USE_OUTREG      => false
   )
   port map (
      CLK             => CLK,
      RESET           => RESET,
      
      IN_DATA         => rd_data_in,
      IN_SOF_N        => rd_sof_n,
      IN_EOF_N        => rd_eof_n,
      IN_SRC_RDY_N    => rd_src_rdy_n,
      IN_DST_RDY_N    => rd_dst_rdy_n,
      
      OUT_DATA        => rd_pipe_data_in,
      OUT_SOF_N       => rd_pipe_sof_n,
      OUT_EOF_N       => rd_pipe_eof_n,
      OUT_SRC_RDY_N   => rd_pipe_src_rdy_n,
      OUT_DST_RDY_N   => rd_pipe_dst_rdy_n
   );
   
   U_cpl_pipe: entity work.IB_PIPE
   generic map (
      DATA_WIDTH      => DATA_WIDTH,
      USE_OUTREG      => false,
      FAKE_PIPE       => true
   )
   port map (
      CLK             => CLK,
      RESET           => RESET,
      
      IN_DATA         => cpl_data,
      IN_SOF_N        => cpl_sof_n,
      IN_EOF_N        => cpl_eof_n,
      IN_SRC_RDY_N    => cpl_src_rdy_n,
      IN_DST_RDY_N    => cpl_dst_rdy_n,
      
      OUT_DATA        => cpl_pipe_data,
      OUT_SOF_N       => cpl_pipe_sof_n,
      OUT_EOF_N       => cpl_pipe_eof_n,
      OUT_SRC_RDY_N   => cpl_pipe_src_rdy_n,
      OUT_DST_RDY_N   => cpl_pipe_dst_rdy_n
   );
   
   -- -------------------------------------------------------------------------
   --                            READ CONTROLLER                             --
   -- -------------------------------------------------------------------------

   U_read_ctrl : entity work.GICS_IB_ENDPOINT_READ_CTRL
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH      => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH      => ADDR_WIDTH,
      -- Data alignment (to dst. address)
      DATA_REORDER    => DATA_REORDER,
      -- The number of reads in-process
      READ_IN_PROCESS => READ_IN_PROCESS,
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE       => READ_TYPE
   )
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK, 
      RESET          => RESET,

      -- Input Interface ----------------------------------
      IN_DATA        => rd_pipe_data_in,
      IN_SOF_N       => rd_pipe_sof_n,
      IN_EOF_N       => rd_pipe_eof_n,
      IN_SRC_RDY_N   => rd_pipe_src_rdy_n,
      IN_DST_RDY_N   => rd_pipe_dst_rdy_n,

      -- Output Interface ---------------------------------
      OUT_DATA       => cpl_data,
      OUT_SOF_N      => cpl_sof_n,
      OUT_EOF_N      => cpl_eof_n,
      OUT_SRC_RDY_N  => cpl_src_rdy_n,
      OUT_DST_RDY_N  => cpl_dst_rdy_n,

      -- Read Interface -----------------------------------
      RD_REQ         => RD_REQ,        
      RD_ARDY_ACCEPT => RD_ARDY_ACCEPT,
      RD_ADDR        => RD_ADDR,       
      RD_BE          => RD_BE,         
      RD_LENGTH      => RD_LENGTH,     
      RD_SOF         => RD_SOF,        
      RD_EOF         => RD_EOF,        
                                      
      RD_DATA        => RD_DATA,       
      RD_SRC_RDY     => RD_SRC_RDY,    
      RD_DST_RDY     => RD_DST_RDY,    
                     
     -- BM Done Interface ---------------------------------
      BM_TAG         => cpl_tag,
      BM_TAG_VLD     => cpl_tag_vld,
      
      -- Strict unit interface ----------------------------
      RD_EN          => rd_en,
      RD_COMPLETE    => rd_complete
   );
   
   -- -------------------------------------------------------------------------
   --                            UPSTREAM BUFFER                             --
   -- -------------------------------------------------------------------------

   U_up_buf : entity work.IB_ENDPOINT_UP_BUF
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH         => DATA_WIDTH,     
      -- Output Buffer Size
      OUTPUT_BUFFER_SIZE => OUTPUT_BUFFER_SIZE
   )
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Input Interface ----------------------------------
      IN_DATA       => up_data,
      IN_SOF_N      => up_sof_n,
      IN_EOF_N      => up_eof_n,
      IN_SRC_RDY_N  => up_src_rdy_n,
      IN_DST_RDY_N  => up_dst_rdy_n,
                    
      -- Output Interface ---------------------------------
      OUT_DATA      => IB_UP_DATA,     
      OUT_SOF_N     => IB_UP_SOF_N,    
      OUT_EOF_N     => IB_UP_EOF_N,    
      OUT_SRC_RDY_N => IB_UP_SRC_RDY_N,
      OUT_DST_RDY_N => IB_UP_DST_RDY_N
   );
                              
end pipelined;   



