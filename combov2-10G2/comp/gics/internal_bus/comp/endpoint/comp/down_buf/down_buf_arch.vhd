--
-- down_buf_arch.vhd : Internal Bus Endpoint Down Buffer architecture
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
--     ARCHITECTURE DECLARATION  --  Internal Bus Endpoint Down Buffer       --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_down_buf_arch of IB_ENDPOINT_DOWN_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- ------------------------------------------------------------------------- 

   -- address decoder signals -----------------------------
   signal addr_dec_in_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal addr_dec_in_sof_n      : std_logic;
   signal addr_dec_in_eof_n      : std_logic;
   signal addr_dec_in_sof_n_aux  : std_logic;
   signal addr_dec_in_eof_n_aux  : std_logic;
   signal addr_dec_in_src_rdy_n  : std_logic;
   signal addr_dec_in_dst_rdy_n  : std_logic;
                           
   signal addr_dec_out_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal addr_dec_out_sof_n     : std_logic;
   signal addr_dec_out_eof_n     : std_logic;
   signal addr_dec_out_src_rdy_n : std_logic;
   signal addr_dec_out_dst_rdy_n : std_logic;
                           
   signal addr_dec_out_req       : std_logic;
   signal addr_dec_out_drop      : std_logic;
   signal addr_dec_out_ack       : std_logic;
   
   -- fetch marker signals --------------------------------
   signal tag_vld                : std_logic;
   signal type_vld               : std_logic;
   signal src_addr_vld           : std_logic;
   signal dst_addr_vld           : std_logic;

   -- down fsm signals ------------------------------------
   signal fsm_rd_sof_n           : std_logic;
   signal fsm_rd_eof_n           : std_logic;
   signal fsm_rd_src_rdy_n       : std_logic;
   signal fsm_rd_dst_rdy_n       : std_logic;
  
begin

   -- -------------------------------------------------------------------------
   --                              INPUT BUFFER                              --
   -- -------------------------------------------------------------------------

   -- WITHOUT INPUT BUFFER ----------------------------------------------------
   INPUT_BUFFER_GEN0: if (INPUT_BUFFER_SIZE = 0) generate

      addr_dec_in_data      <= IB_DATA;
      addr_dec_in_sof_n_aux <= IB_SOF_N;
      addr_dec_in_eof_n_aux <= IB_EOF_N;    
      addr_dec_in_src_rdy_n <= IB_SRC_RDY_N;
      
      IB_DST_RDY_N          <= addr_dec_in_dst_rdy_n;
   
   end generate;

   -- WITH IB PIPE ONLY  ------------------------------------------------------
   INPUT_BUFFER_GEN1: if (INPUT_BUFFER_SIZE = 1 or
                          INPUT_BUFFER_SIZE = 2) generate

      U_input_pipe : entity work.IB_PIPE
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         USE_OUTREG     => (INPUT_BUFFER_SIZE = 2)
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         
         IN_DATA        => IB_DATA,
         IN_SOF_N       => IB_SOF_N,
         IN_EOF_N       => IB_EOF_N,    
         IN_SRC_RDY_N   => IB_SRC_RDY_N,
         IN_DST_RDY_N   => IB_DST_RDY_N,
                        
         OUT_DATA       => addr_dec_in_data,     
         OUT_SOF_N      => addr_dec_in_sof_n_aux,
         OUT_EOF_N      => addr_dec_in_eof_n_aux,
         OUT_SRC_RDY_N  => addr_dec_in_src_rdy_n,
         OUT_DST_RDY_N  => addr_dec_in_dst_rdy_n
      );                
      
   end generate;

   -- WITH INPUT BUFFER -------------------------------------------------------
   INPUT_BUFFER_GEN:  if (INPUT_BUFFER_SIZE > 2) generate

      U_input_buffer : entity work.IB_BUFFER_SH
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => INPUT_BUFFER_SIZE
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,
         
         IN_DATA        => IB_DATA,
         IN_SOF_N       => IB_SOF_N,
         IN_EOF_N       => IB_EOF_N,    
         IN_SRC_RDY_N   => IB_SRC_RDY_N,
         IN_DST_RDY_N   => IB_DST_RDY_N,
                        
         OUT_DATA       => addr_dec_in_data,     
         OUT_SOF_N      => addr_dec_in_sof_n_aux,
         OUT_EOF_N      => addr_dec_in_eof_n_aux,
         OUT_SRC_RDY_N  => addr_dec_in_src_rdy_n,
         OUT_DST_RDY_N  => addr_dec_in_dst_rdy_n
      );                
      
   end generate;   
   
   -- SOF and EOF active only when SRC_RDY
   addr_dec_in_sof_n <= addr_dec_in_sof_n_aux or addr_dec_in_src_rdy_n;
   addr_dec_in_eof_n <= addr_dec_in_eof_n_aux or addr_dec_in_src_rdy_n;
   
   -- -------------------------------------------------------------------------
   --                            ADDRESS DECODER                             --
   -- -------------------------------------------------------------------------   

   -- WITHOUT ADDRESS DECODER -------------------------------------------------
   ADDRESS_DECODER_GEN_NO:  if (CONNECTED_TO = SWITCH_MASTER) generate

      addr_dec_out_data      <= addr_dec_in_data;    
      addr_dec_out_sof_n     <= addr_dec_in_sof_n;    
      addr_dec_out_eof_n     <= addr_dec_in_eof_n;    
      addr_dec_out_src_rdy_n <= addr_dec_in_src_rdy_n;
   
      addr_dec_in_dst_rdy_n  <= addr_dec_out_dst_rdy_n;

      addr_dec_out_req       <= '1';
      addr_dec_out_drop      <= '0';
      
   end generate;      

   -- WITH ADDRESS DECODER ----------------------------------------------------
   ADDRESS_DECODER_GEN_YES: if (not (CONNECTED_TO = SWITCH_MASTER)) generate

      U_addr_dec : entity work.IB_ENDPOINT_ADDR_DEC
      generic map (
         DATA_WIDTH     => DATA_WIDTH,    
         ENDPOINT_BASE  => ENDPOINT_BASE, 
         ENDPOINT_LIMIT => ENDPOINT_LIMIT
      ) 
      port map (
         CLK            => CLK,
         RESET          => RESET,
                        
         IN_DATA        => addr_dec_in_data,     
         IN_SOF_N       => addr_dec_in_sof_n,    
         IN_EOF_N       => addr_dec_in_eof_n,    
         IN_SRC_RDY_N   => addr_dec_in_src_rdy_n,
         IN_DST_RDY_N   => addr_dec_in_dst_rdy_n,
                        
         OUT_DATA       => addr_dec_out_data,     
         OUT_SOF_N      => addr_dec_out_sof_n,    
         OUT_EOF_N      => addr_dec_out_eof_n,    
         OUT_SRC_RDY_N  => addr_dec_out_src_rdy_n,
         OUT_DST_RDY_N  => addr_dec_out_dst_rdy_n,
                        
         OUT_REQ        => addr_dec_out_req, 
         OUT_DROP       => addr_dec_out_drop,
         OUT_ACK        => addr_dec_out_ack
      );
   
   end generate;   

   -- -------------------------------------------------------------------------
   --                                SWAPPER                                 --
   -- -------------------------------------------------------------------------   

   U_swapper : entity work.IB_ENDPOINT_SWAPPER
   generic map (
      DATA_WIDTH    => DATA_WIDTH
   )
   port map (
      CLK           => CLK,
      RESET         => RESET,
                    
      IN_DATA       => addr_dec_out_data,     
      IN_SOF_N      => fsm_rd_sof_n,    
      IN_EOF_N      => fsm_rd_eof_n,    
      IN_SRC_RDY_N  => fsm_rd_src_rdy_n,
      IN_DST_RDY_N  => fsm_rd_dst_rdy_n,
                    
      OUT_DATA      => RD_DATA,
      OUT_SOF_N     => RD_SOF_N,    
      OUT_EOF_N     => RD_EOF_N,    
      OUT_SRC_RDY_N => RD_SRC_RDY_N,
      OUT_DST_RDY_N => RD_DST_RDY_N,
                    
      DST_ADDR_VLD  => dst_addr_vld,
      SRC_ADDR_VLD  => src_addr_vld,
      TYPE_VLD      => type_vld
   );
   
   -- -------------------------------------------------------------------------
   --                              FETCH MARKER                              --
   -- -------------------------------------------------------------------------   

   U_fetch_marker : entity work.IB_ENDPOINT_DOWN_BUF_FETCH_MARKER
   generic map (
      DATA_WIDTH   => DATA_WIDTH
   ) 
   port map (
      CLK          => CLK,
      RESET        => RESET,

      SOF_N        => addr_dec_out_sof_n,    
      EOF_N        => addr_dec_out_eof_n,    
      SRC_RDY_N    => addr_dec_out_src_rdy_n,
      DST_RDY_N    => addr_dec_out_dst_rdy_n,

      TAG_VLD      => tag_vld,
      TYPE_VLD     => type_vld,
      SRC_ADDR_VLD => src_addr_vld,
      DST_ADDR_VLD => dst_addr_vld
   );

   -- -------------------------------------------------------------------------
   --                                DOWN FSM                                --
   -- -------------------------------------------------------------------------   

   U_down_fsm : entity work.IB_ENDPOINT_DOWN_FSM
   generic map (
      DATA_WIDTH   => DATA_WIDTH
   )    
   port map (
      CLK          => CLK,
      RESET        => RESET,

      IB_DATA      => addr_dec_out_data,
      IB_SOF_N     => addr_dec_out_sof_n,    
      IB_EOF_N     => addr_dec_out_eof_n,    
      IB_SRC_RDY_N => addr_dec_out_src_rdy_n,
      IB_DST_RDY_N => addr_dec_out_dst_rdy_n,

      IB_REQ       => addr_dec_out_req, 
      IB_DROP      => addr_dec_out_drop,
      IB_ACK       => addr_dec_out_ack,
                   
      RD_SOF_N     => fsm_rd_sof_n,    
      RD_EOF_N     => fsm_rd_eof_n,    
      RD_SRC_RDY_N => fsm_rd_src_rdy_n,
      RD_DST_RDY_N => fsm_rd_dst_rdy_n,

      WR_DATA      => WR_DATA,
      WR_SOF_N     => WR_SOF_N,    
      WR_EOF_N     => WR_EOF_N,    
      WR_SRC_RDY_N => WR_SRC_RDY_N,
      WR_DST_RDY_N => WR_DST_RDY_N
   );

   -- -------------------------------------------------------------------------
   --                                DONE UNIT                               --
   -- -------------------------------------------------------------------------   

   U_done_unit : entity work.IB_ENDPOINT_DOWN_BUF_DONE_UNIT
   generic map (
      DATA_WIDTH   => DATA_WIDTH
   ) 
   port map (
      CLK          => CLK,
      RESET        => RESET,
                   
      IN_DATA      => addr_dec_out_data,     
      IN_SOF_N     => addr_dec_out_sof_n,       
      IN_EOF_N     => addr_dec_out_eof_n,       
      IN_SRC_RDY_N => addr_dec_out_src_rdy_n,   
      IN_DST_RDY_N => addr_dec_out_dst_rdy_n,   

      IN_TAG_VLD   => tag_vld,
      IN_TYPE_VLD  => type_vld,
      IN_REQ       => addr_dec_out_req,
                   
      OUT_TAG      => BM_TAG,
      OUT_TAG_VLD  => BM_TAG_VLD,    
      OUT_DONE     => BM_DONE       
   );              
                   
end ib_endpoint_down_buf_arch;   



