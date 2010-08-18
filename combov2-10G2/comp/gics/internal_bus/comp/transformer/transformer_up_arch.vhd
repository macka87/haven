--
-- transformer_up_arch.vhd : IB Transformer Up architecture
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
use work.ib_transformer_pkg.all;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  IB Transformer Up               --
-- ----------------------------------------------------------------------------

architecture ib_transformer_up_arch of IB_TRANSFORMER_UP is
  
   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- ------------------------------------------------------------------------- 

   signal buf_data        : std_logic_vector(IN_DATA_WIDTH-1 downto 0); 
   signal buf_sof_n       : std_logic;
   signal buf_eof_n       : std_logic;
   signal buf_src_rdy_n   : std_logic;
   signal buf_dst_rdy_n   : std_logic;
   
   signal buf_sof_n_aux   : std_logic;
   signal buf_eof_n_aux   : std_logic;
                          
   signal pipe_data       : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal pipe_sof_n      : std_logic;
   signal pipe_eof_n      : std_logic;
   signal pipe_src_rdy_n  : std_logic;
   signal pipe_dst_rdy_n  : std_logic;
                          
   signal reg_data        : std_logic_vector(OUT_DATA_WIDTH-IN_DATA_WIDTH-1 downto 0);
   signal len_align_we    : std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
   signal addr_align_we   : std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
   signal payload_flag_we : std_logic;
   signal reg_data_we     : std_logic;
   signal first_part_sel  : std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
   signal cnt_parts_rst   : std_logic;
   signal cnt_parts_ce    : std_logic;
   signal cnt_parts_we    : std_logic;
   signal cnt_parts       : std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
   signal last_part_sel   : std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
   signal payload_flag    : std_logic;
   signal header_last     : std_logic; 
  
begin

   -- -------------------------------------------------------------------------
   --                               DATA PATH                                --
   -- ------------------------------------------------------------------------- 

   -- INPUT BUFFER ------------------------------------------------------------
   U_input_buffer : entity work.IB_TRANSFORMER_BUFFER
   generic map (
      DATA_WIDTH     => IN_DATA_WIDTH,
      ITEMS          => IN_BUFFER_ITEMS
   )
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK,    
      RESET          => RESET,
      
      -- Input interface ----------------------------------
      IN_DATA        => IN_DATA,     
      IN_SOF_N       => IN_SOF_N,    
      IN_EOF_N       => IN_EOF_N,    
      IN_SRC_RDY_N   => IN_SRC_RDY_N,
      IN_DST_RDY_N   => IN_DST_RDY_N,
                     
      -- Output interface ---------------------------------
      OUT_DATA       => buf_data,
      OUT_SOF_N      => buf_sof_n_aux,
      OUT_EOF_N      => buf_eof_n_aux,
      OUT_SRC_RDY_N  => buf_src_rdy_n,
      OUT_DST_RDY_N  => buf_dst_rdy_n
   );
   
   buf_sof_n <= buf_sof_n_aux or buf_src_rdy_n;
   buf_eof_n <= buf_eof_n_aux or buf_src_rdy_n;
   
   -- DATA REGISTER -----------------------------------------------------------
   reg_datap: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
      
         for i in 0 to (OUT_DATA_WIDTH/IN_DATA_WIDTH)-2 loop
            if (cnt_parts = i and reg_data_we = '1') then
               reg_data((i+1)*IN_DATA_WIDTH -1 downto i*IN_DATA_WIDTH) <= buf_data;
            end if;
         end loop;           
                 
      end if;         
   end process;

   pipe_data <= buf_data&reg_data;

   -- OUTPUT PIPE -------------------------------------------------------------
   U_output_pipe : entity work.IB_TRANSFORMER_BUFFER
   generic map (
      DATA_WIDTH     => OUT_DATA_WIDTH,
      ITEMS          => boolean2integer(OUT_PIPE)
   )
   port map (
      -- Common interface ---------------------------------
      CLK            => CLK,    
      RESET          => RESET,
      
      -- Input interface ----------------------------------
      IN_DATA        => pipe_data, 
      IN_SOF_N       => pipe_sof_n, 
      IN_EOF_N       => pipe_eof_n, 
      IN_SRC_RDY_N   => pipe_src_rdy_n, 
      IN_DST_RDY_N   => pipe_dst_rdy_n,
                     
      -- Output interface ---------------------------------
      OUT_DATA       => OUT_DATA,     
      OUT_SOF_N      => OUT_SOF_N,    
      OUT_EOF_N      => OUT_EOF_N,    
      OUT_SRC_RDY_N  => OUT_SRC_RDY_N,
      OUT_DST_RDY_N  => OUT_DST_RDY_N
   );   

   -- -------------------------------------------------------------------------
   --                              CONTROL LOGIC                             --
   -- -------------------------------------------------------------------------

   -- FETCH MARKER ------------------------------------------------------------
   U_fetch_marker : entity work.IB_TRANSFORMER_FETCH_MARKER
   generic map (
      IN_DATA_WIDTH   => IN_DATA_WIDTH,
      OUT_DATA_WIDTH  => OUT_DATA_WIDTH 
   )
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,

      -- IB interface -------------------------------------
      SOF_N           => buf_sof_n,
      EOF_N           => buf_eof_n,
      SRC_RDY_N       => buf_src_rdy_n,
      DST_RDY_N       => buf_dst_rdy_n,

      -- Control Interface --------------------------------
      LEN_ALIGN_WE    => len_align_we,
      ADDR_ALIGN_WE   => addr_align_we,
      PAYLOAD_FLAG_WE => payload_flag_we,
      REG_DATA_WE     => reg_data_we,
      HEADER_LAST     => header_last
   );

   -- UNPACKER ----------------------------------------------------------------
   U_unpacker : entity work.IB_TRANSFORMER_UNPACKER
   generic map (
      IN_DATA_WIDTH   => IN_DATA_WIDTH,
      OUT_DATA_WIDTH  => OUT_DATA_WIDTH    
   )
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,
                      
      -- Input interface ----------------------------------
      DATA            => buf_data,
      
      -- Output Interface ---------------------------------
      FIRST_PART_SEL  => first_part_sel,
      LAST_PART_SEL   => last_part_sel,
      PAYLOAD_FLAG    => payload_flag,

      -- Control Interface --------------------------------
      LEN_ALIGN_WE    => len_align_we,
      ADDR_ALIGN_WE   => addr_align_we,
      PAYLOAD_FLAG_WE => payload_flag_we
   );
 
   -- PARTS COUNTER -----------------------------------------------------------
   U_counter : entity work.IB_TRANSFORMER_COUNTER
   generic map (
      IN_DATA_WIDTH   => IN_DATA_WIDTH,
      OUT_DATA_WIDTH  => OUT_DATA_WIDTH  
   )
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,
   
      -- Control interface --------------------------------      
      RST             => cnt_parts_rst,
      CE              => cnt_parts_ce,
      WE              => cnt_parts_we,

      -- Data interface -----------------------------------
      COUNTER_IN      => first_part_sel,
      COUNTER_OUT     => cnt_parts
   );

   -- UP FSM ------------------------------------------------------------------
   U_up_fsm : entity work.IB_TRANSFORMER_UP_FSM
   generic map (
      IN_DATA_WIDTH   => IN_DATA_WIDTH,
      OUT_DATA_WIDTH  => OUT_DATA_WIDTH  
   )
   port map (
      -- Common interface ---------------------------------
      CLK             => CLK,
      RESET           => RESET,
 
      -- IN IB interface ----------------------------------
      IN_SOF_N        => buf_sof_n,
      IN_EOF_N        => buf_eof_n,
      IN_SRC_RDY_N    => buf_src_rdy_n,
      IN_DST_RDY_N    => buf_dst_rdy_n,

      -- OUT IB interface ---------------------------------
      OUT_SOF_N       => pipe_sof_n, 
      OUT_EOF_N       => pipe_eof_n, 
      OUT_SRC_RDY_N   => pipe_src_rdy_n,
      OUT_DST_RDY_N   => pipe_dst_rdy_n,

      -- Control interface --------------------------------
      CNT_PARTS_RST   => cnt_parts_rst,
      CNT_PARTS_CE    => cnt_parts_ce,
      CNT_PARTS_WE    => cnt_parts_we,
      CNT_PARTS       => cnt_parts,
      PAYLOAD_FLAG    => payload_flag,
      HEADER_LAST     => header_last    
   );   
                                           
end ib_transformer_up_arch;  



