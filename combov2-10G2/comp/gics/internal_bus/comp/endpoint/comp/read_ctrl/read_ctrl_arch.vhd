--
-- read_ctrl_arch.vhd : Internal Bus Endpoint Read Controller architecture
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
--    ARCHITECTURE DECLARATION  --  Internal Bus Endpoint Read Controller    --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_ctrl_arch of GICS_IB_ENDPOINT_READ_CTRL is

   -- -------------------------------------------------------------------------
   --                          Constant declaration                          --
   -- -------------------------------------------------------------------------
   
   constant ZEROS : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------   

   signal cpl_count     : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
   signal cpl_len_align : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal cpl_src_align : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal cpl_dst_align : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal cpl_tag       : std_logic_vector( 7 downto 0);
   signal cpl_done_flag : std_logic;

   signal unpck_hbuf_re : std_logic;
   signal unpck_hbuf_we : std_logic;
   signal hbuf_full     : std_logic;
   signal pck_hbuf_full : std_logic;
   signal unpck_hbuf_full : std_logic;
   
   signal count         : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
   signal len_align     : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal dst_align     : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal src_align     : std_logic_vector(align_width(DATA_WIDTH)-1 downto 0);
   signal tag           : std_logic_vector( 7 downto 0);
   signal done_flag     : std_logic;

   signal length_we     : std_logic_vector(length_we_width(DATA_WIDTH)-1 downto 0);   
   signal dst_addr_we   : std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);
   signal src_addr_we   : std_logic_vector(addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);
   signal tag_we        : std_logic;
   signal done_flag_we  : std_logic;
   signal transfer      : std_logic;
   signal header_last   : std_logic;
   signal addr_ce       : std_logic;
   signal count_ce      : std_logic;

   signal in_dst_rdy_n_aux  : std_logic;   
   signal RD_SOF_aux        : std_logic;
   signal RD_EOF_aux        : std_logic; 
   signal RD_REQ_aux        : std_logic; 

   signal align_in_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal align_in_src_rdy  : std_logic;
   signal align_in_dst_rdy  : std_logic;
                                                         
   signal align_out_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal align_out_sof     : std_logic;
   signal align_out_eof     : std_logic;
   signal align_out_src_rdy : std_logic;
   signal align_out_dst_rdy : std_logic;

   signal cpl_header        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal cpl_header_sof    : std_logic;
   signal cpl_header_eof    : std_logic;
   signal cpl_header_vld    : std_logic;
   signal cpl_header_re     : std_logic;
   
begin                   
                        
   -- ********************************************************************** --
   -- ***************               READ PART                *************** --
   -- ********************************************************************** --

   -- -------------------------------------------------------------------------
   --                              FETCH MARKER                              --
   -- -------------------------------------------------------------------------

   U_fetch_marker: entity work.IB_ENDPOINT_READ_CTRL_FETCH_MARKER
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH    => ADDR_WIDTH      
   )
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- IB interface -------------------------------------
      SOF_N         => IN_SOF_N,    
      EOF_N         => IN_EOF_N,    
      SRC_RDY_N     => IN_SRC_RDY_N,
      DST_RDY_N     => IN_DST_RDY_N_aux,

      -- Control Interface --------------------------------
      LENGTH_WE     => length_we,
      ADDR32_WE     => dst_addr_we,
      ADDR64_WE     => src_addr_we,
      TAG_WE        => tag_we,
      DONE_FLAG_WE  => done_flag_we,
      TRANSFER      => transfer,
      HEADER_LAST   => header_last
   );
   
   -- -------------------------------------------------------------------------
   --                                UNPACKER                                --
   -- -------------------------------------------------------------------------

   U_unpacker: entity work.IB_UNPACKER
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

      -- Input interface ----------------------------------
      DATA         => IN_DATA,

      -- Output Interface ---------------------------------
      LENGTH       => RD_LENGTH,
      COUNT        => count,
      ADDR32       => open,
      ADDR64       => RD_ADDR,
      LEN_ALIGN    => len_align,
      A32_ALIGN    => dst_align,
      A64_ALIGN    => src_align,
      TAG          => tag,
      DONE_FLAG    => done_flag,

      -- Control Interface --------------------------------
      LENGTH_WE    => length_we,
      ADDR32_WE    => dst_addr_we,
      ADDR64_WE    => src_addr_we,
      ADDR32_CE    => '0',
      ADDR64_CE    => addr_ce,
      COUNT_CE     => count_ce,
      TAG_WE       => tag_we,
      DONE_FLAG_WE => done_flag_we,
      HEADER_LAST  => header_last
   );

   -- -------------------------------------------------------------------------
   --                          BYTE ENABLE GENERATOR                         --
   -- -------------------------------------------------------------------------

   BE_GEN_YES:  if (DATA_WIDTH > 8) generate

      U_be_gen : entity work.IB_BE_GEN
      generic map (
         -- Data Width (8-128)
         DATA_WIDTH   => DATA_WIDTH
      )
      port map (
         -- Common interface ------------------------------
         CLK          => CLK,  
         RESET        => RESET,
         
         -- Input Interface -------------------------------
         LENGTH_ALIGN => len_align,
         ADDR_ALIGN   => src_align,
         SOF          => RD_SOF_aux,
         EOF          => RD_EOF_aux,
         
         -- Output Interface ------------------------------
         BE           => RD_BE
      );              

   end generate; 
   
   -- -------------------------------------------------------------------------
   --                               READ FSM                                 --
   -- -------------------------------------------------------------------------

   U_read_fsm : entity work.GICS_IB_ENDPOINT_READ_FSM
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH     => DATA_WIDTH,
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE      => READ_TYPE
   ) 
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK,
      RESET          => RESET,
 
      -- IB interface -------------------------------------
      IB_SOF_N       => IN_SOF_N,    
      IB_EOF_N       => IN_EOF_N,    
      IB_SRC_RDY_N   => IN_SRC_RDY_N,
      IB_DST_RDY_N   => IN_DST_RDY_N_aux,

      -- RD interface -------------------------------------
      RD_SOF         => RD_SOF_aux,        
      RD_EOF         => RD_EOF_aux,        
      RD_REQ         => RD_REQ_aux,   
      RD_ARDY_ACCEPT => RD_ARDY_ACCEPT,

      -- Control interface --------------------------------
      COUNT          => count,
      HEADER_LAST    => header_last,
      HBUF_FULL      => hbuf_full,
      HBUF_WE        => unpck_hbuf_we,
      COUNT_CE       => count_ce,
      ADDR_CE        => addr_ce,
      
      -- Strict unit interface ----------------------------
      RD_EN          => RD_EN
   );

   RD_SOF <= RD_SOF_aux;
   RD_EOF <= RD_EOF_aux;
   RD_REQ <= RD_REQ_aux;

   IN_DST_RDY_N <= IN_DST_RDY_N_aux;    
   
   RD_COMPLETE <= RD_EOF_aux and RD_REQ_aux and RD_ARDY_ACCEPT;
   
   -- ********************************************************************** --
   -- ***************              BUFFER PART               *************** --
   -- ********************************************************************** --

   -- -------------------------------------------------------------------------
   --                          PACKED HEADER BUFFER                          --
   -- -------------------------------------------------------------------------

   U_pck_hbuf : entity work.IB_ENDPOINT_READ_CTRL_PCK_HBUF 
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- The number of items to be stored
      ITEMS         => ib_endpoint_read_ctrl_pck_hbuf_depth(READ_IN_PROCESS, DATA_WIDTH)
   )
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,   
      RESET         => RESET,

      -- Input interface ----------------------------------
      IN_DATA       => IN_DATA,
      IN_SOF_N      => IN_SOF_N,
      IN_EOF_N      => IN_EOF_N,
      IN_FULL       => pck_hbuf_full,
      IN_WE         => transfer,

      -- Output interface ---------------------------------
      OUT_DATA      => cpl_header,
      OUT_SOF       => cpl_header_sof,   
      OUT_EOF       => cpl_header_eof,
      OUT_DATA_VLD  => cpl_header_vld,
      OUT_RE        => cpl_header_re
   );

   -- -------------------------------------------------------------------------
   --                         UNPACKED HEADER BUFFER                         --
   -- -------------------------------------------------------------------------

   U_unpck_hbuf : entity work.IB_ENDPOINT_READ_CTRL_UNPCK_HBUF
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- The number of items to be stored
      ITEMS         => ib_endpoint_read_ctrl_unpck_hbuf_depth(READ_IN_PROCESS, DATA_WIDTH)  
   ) 
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,
      RESET         => RESET,

      -- Input interface ----------------------------------
      IN_COUNT      => count,
      IN_LEN_ALIGN  => len_align,
      IN_SRC_ALIGN  => src_align,
      IN_DST_ALIGN  => dst_align,
      IN_TAG        => tag,
      IN_DONE_FLAG  => done_flag,
      
      IN_WE         => unpck_hbuf_we,
      IN_FULL       => unpck_hbuf_full,
                    
      -- Output interface ---------------------------------
      OUT_COUNT     => cpl_count,
      OUT_LEN_ALIGN => cpl_len_align,
      OUT_SRC_ALIGN => cpl_src_align,
      OUT_DST_ALIGN => cpl_dst_align,
      OUT_TAG       => cpl_tag,
      OUT_DONE_FLAG => cpl_done_flag,
                                     
      OUT_RE        => unpck_hbuf_re
   );               

   hbuf_full <= pck_hbuf_full or unpck_hbuf_full;
   
   -- ********************************************************************** --
   -- ***************            COMPLETION PART             *************** --
   -- ********************************************************************** --

   -- -------------------------------------------------------------------------
   --                           COMPLETION BUFFER                            --
   -- -------------------------------------------------------------------------

   U_cpl_buf : entity work.IB_ENDPOINT_READ_CTRL_CPL_BUF
   generic map (
      -- Data Width (1-128)
      DATA_WIDTH    => DATA_WIDTH,
      -- The number of items to be stored
      ITEMS         => 16    
   )
   port map (
      -- Common interface ---------------------------------
      CLK           => CLK,  
      RESET         => RESET,

      -- Input interface ----------------------------------
      IN_DATA       => RD_DATA,
      IN_SRC_RDY    => RD_SRC_RDY,
      IN_DST_RDY    => RD_DST_RDY,

      -- Output interface ---------------------------------
      OUT_DATA      => align_in_data,
      OUT_SRC_RDY   => align_in_src_rdy,
      OUT_DST_RDY   => align_in_dst_rdy
   );

   -- -------------------------------------------------------------------------
   --                              ALIGN UNIT                                --
   -- -------------------------------------------------------------------------

   -- alignment function is switched OFF ------------------
   DATA_REORDER_NO:  if (not DATA_REORDER or DATA_WIDTH = 8) generate
   
      U_align_unit_fake : entity work.IB_ENDPOINT_READ_CTRL_ALIGN_UNIT_FAKE
      generic map (
         DATA_WIDTH    => DATA_WIDTH
      )
      port map (
         -- Common interface ------------------------------
         CLK           => CLK,
         RESET         => RESET,

         -- Control interface -----------------------------
         COUNT         => cpl_count,
         NEXT_TRANS    => unpck_hbuf_re,

         -- Input interface -------------------------------
         IN_DATA       => align_in_data,
         IN_SRC_RDY    => align_in_src_rdy,
         IN_DST_RDY    => align_in_dst_rdy,

         -- Output interface ------------------------------
         OUT_DATA      => align_out_data,
         OUT_SOF       => align_out_sof,
         OUT_EOF       => align_out_eof,
         OUT_SRC_RDY   => align_out_src_rdy,
         OUT_DST_RDY   => align_out_dst_rdy
      );
   
   end generate;

   -- alignment function is switched ON -------------------
   DATA_REORDER_YES:  if (DATA_REORDER and DATA_WIDTH > 8) generate
   
      U_align_unit : entity work.IB_ENDPOINT_READ_CTRL_ALIGN_UNIT
      generic map (
         DATA_WIDTH    => DATA_WIDTH
      )
      port map (
         -- Common interface ------------------------------
         CLK           => CLK,
         RESET         => RESET,

         -- Control interface -----------------------------
         COUNT         => cpl_count,
         LEN_ALIGN     => cpl_len_align,
         SRC_ALIGN     => cpl_src_align,
         DST_ALIGN     => cpl_dst_align,
         NEXT_TRANS    => unpck_hbuf_re,

         -- Input interface -------------------------------
         IN_DATA       => align_in_data,
         IN_SRC_RDY    => align_in_src_rdy,
         IN_DST_RDY    => align_in_dst_rdy,

         -- Output interface ------------------------------
         OUT_DATA      => align_out_data,
         OUT_SOF       => align_out_sof,
         OUT_EOF       => align_out_eof,
         OUT_SRC_RDY   => align_out_src_rdy,
         OUT_DST_RDY   => align_out_dst_rdy
      );
   
   end generate;   

   -- -------------------------------------------------------------------------
   --                           OUTPUT MULTIPLEXOR                           --
   -- -------------------------------------------------------------------------

   with cpl_header_re select OUT_DATA <= cpl_header     when '1',
                                         align_out_data when others;
   
   -- -------------------------------------------------------------------------
   --                             COMPLETION FSM                             --
   -- -------------------------------------------------------------------------

   U_cpl_fsm : entity work.IB_ENDPOINT_CPL_FSM
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH     => DATA_WIDTH
   )
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK,
      RESET          => RESET,

      -- Header interface ---------------------------------
      HEADER_SOF     => cpl_header_sof,
      HEADER_EOF     => cpl_header_eof,
      HEADER_SRC_RDY => cpl_header_vld,
      HEADER_DST_RDY => cpl_header_re,

      -- Data Interface -----------------------------------
      DATA_SOF       => align_out_sof,
      DATA_EOF       => align_out_eof,
      DATA_SRC_RDY   => align_out_src_rdy,
      DATA_DST_RDY   => align_out_dst_rdy,

      -- IB Interface -------------------------------------
      IB_SOF_N       => OUT_SOF_N,    
      IB_EOF_N       => OUT_EOF_N,    
      IB_SRC_RDY_N   => OUT_SRC_RDY_N,
      IB_DST_RDY_N   => OUT_DST_RDY_N
   );

   -- -------------------------------------------------------------------------
   --                           BM DONE INTERFACE                            --
   -- -------------------------------------------------------------------------

   BM_TAG     <= cpl_tag;
   BM_TAG_VLD <= cpl_done_flag and unpck_hbuf_re;
                            
end ib_endpoint_read_ctrl_arch;   



