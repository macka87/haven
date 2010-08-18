-- fl_composer.vhd: Composes FL from headers/footers and payload
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture FL_COMPOSER_ARCH of FL_COMPOSER is

   -- Signals declaration
   -- Multiplexers
   signal mx_data          : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal mx_rem           : std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal mx_sop_n         : std_logic;
   signal mx_eop_n         : std_logic;
   signal mx_src_rdy_n     : std_logic;

   -- Composed FrameLink
   signal fl_composed_data : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal fl_composed_rem  : std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal fl_composed_sof_n      : std_logic;
   signal fl_composed_sop_n      : std_logic;
   signal fl_composed_eop_n      : std_logic;
   signal fl_composed_eof_n      : std_logic;
   signal fl_composed_src_rdy_n  : std_logic;
   signal fl_composed_dst_rdy_n  : std_logic;

   -- FSM signals
   signal fsm_eop_n        : std_logic;
   signal fsm_heop_n       : std_logic;
   signal fsm_sof_n        : std_logic;
   signal fsm_eof_n        : std_logic;
   signal fifo_sel         : std_logic;


begin

   DEBUG_FIFO_SEL <= fifo_sel;

   -- -------------------------------------------------------------------------
   --                             Input dst_rdy_n
   -- -------------------------------------------------------------------------
   RX_DST_RDY_N  <= fifo_sel or fl_composed_dst_rdy_n;
   
   -- Constant reading from hfifo (otherwise it get full)
   const_read_gen : if (CTRL_HDR_EN = false AND CTRL_FTR_EN = false) generate
      RX_HDST_RDY_N <= '0';
   end generate;
   
   -- Reading from hfifo on request (when header or footer is needed)
   req_read_gen : if (CTRL_HDR_EN = true OR CTRL_FTR_EN = true) generate
      RX_HDST_RDY_N <= not fifo_sel or fl_composed_dst_rdy_n;
   end generate;
   

   -- -------------------------------------------------------------------------
   --                              Multiplexers
   -- -------------------------------------------------------------------------
   
   -- multiplexor mx_data
   mx_datap: process(fifo_sel, RX_DATA, RX_HDATA)
   begin
      case fifo_sel is
         when '0' => mx_data <= RX_DATA;
         when '1' => mx_data <= RX_HDATA;
         when others => mx_data <= (others => 'X');
      end case;
   end process;
   
   -- multiplexor mx_rem
   mx_remp: process(fifo_sel, RX_REM, RX_HREM)
   begin
      case fifo_sel is
         when '0' => mx_rem <= RX_REM;
         when '1' => mx_rem <= RX_HREM;
         when others => mx_rem <= (others => 'X');
      end case;
   end process;
   
   -- multiplexor mx_sop_n
   mx_sop_np: process(fifo_sel, RX_SOP_N, RX_HSOP_N)
   begin
      case fifo_sel is
         when '0' => mx_sop_n <= RX_SOP_N;
         when '1' => mx_sop_n <= RX_HSOP_N;
         when others => mx_sop_n <= 'X';
      end case;
   end process;
   
   -- multiplexor mx_eop_n
   mx_eop_np: process(fifo_sel, RX_EOP_N, RX_HEOP_N)
   begin
      case fifo_sel is
         when '0' => mx_eop_n <= RX_EOP_N;
         when '1' => mx_eop_n <= RX_HEOP_N;
         when others => mx_eop_n <= 'X';
      end case;
   end process;
   
   -- multiplexor mx_src_rdy_n
   mx_src_rdy_np: process(fifo_sel, RX_SRC_RDY_N, RX_HSRC_RDY_N)
   begin
      case fifo_sel is
         when '0' => mx_src_rdy_n <= RX_SRC_RDY_N;
         when '1' => mx_src_rdy_n <= RX_HSRC_RDY_N;
         when others => mx_src_rdy_n <= 'X';
      end case;
   end process;
   

   -- -------------------------------------------------------------------------
   --                         Composed FrameLink
   -- -------------------------------------------------------------------------

   fl_composed_data        <= mx_data;
   fl_composed_rem         <= mx_rem;
   fl_composed_sof_n       <= mx_sop_n or fsm_sof_n;
   fl_composed_sop_n       <= mx_sop_n;
   fl_composed_eop_n       <= mx_eop_n;
   fl_composed_eof_n       <= mx_eop_n or fsm_eof_n;
   fl_composed_src_rdy_n   <= mx_src_rdy_n;


   -- -------------------------------------------------------------------------
   --                                FSM
   -- -------------------------------------------------------------------------

   fsm_eop_n  <= RX_EOP_N or RX_SRC_RDY_N or fl_composed_dst_rdy_n;
   fsm_heop_n <= RX_HEOP_N or RX_HSRC_RDY_N or fl_composed_dst_rdy_n;

   fsm_hpf_gen: if (CTRL_HDR_EN = true AND CTRL_FTR_EN = true) generate
      fsm_hpfi: entity work.fl_composer_fsm_hpf
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            EOP_N          => fsm_eop_n,
            HEOP_N         => fsm_heop_n,
      
            FIFO_SEL       => fifo_sel,
            SOF_N          => fsm_sof_n,
            EOF_N          => fsm_eof_n
         );
   end generate;

   fsm_hp_gen: if (CTRL_HDR_EN = true AND CTRL_FTR_EN = false) generate
      fsm_hpi: entity work.fl_composer_fsm_hp
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            EOP_N          => fsm_eop_n,
            HEOP_N         => fsm_heop_n,
      
            FIFO_SEL       => fifo_sel,
            SOF_N          => fsm_sof_n,
            EOF_N          => fsm_eof_n
         );
   end generate;

   fsm_pf_gen: if (CTRL_HDR_EN = false AND CTRL_FTR_EN = true) generate
      fsm_pfi: entity work.fl_composer_fsm_pf
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            EOP_N          => fsm_eop_n,
            HEOP_N         => fsm_heop_n,
      
            FIFO_SEL       => fifo_sel,
            SOF_N          => fsm_sof_n,
            EOF_N          => fsm_eof_n
         );
   end generate;

   fsm_p_gen: if (CTRL_HDR_EN = false AND CTRL_FTR_EN = false) generate
      fsm_pi: entity work.fl_composer_fsm_p
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            EOP_N          => fsm_eop_n,
            HEOP_N         => fsm_heop_n,
      
            FIFO_SEL       => fifo_sel,
            SOF_N          => fsm_sof_n,
            EOF_N          => fsm_eof_n
         );
   end generate;


   -- -------------------------------------------------------------------------
   --                               FL Relay
   -- -------------------------------------------------------------------------

   flrel_gen: if (FL_RELAY = true) generate
      flreli: entity work.FL_PIPE
         generic map(
            -- FrameLink Data Width
            DATA_WIDTH     => FL_WIDTH_TX,
            USE_OUTREG     => true
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            RX_DATA        => fl_composed_data,
            RX_REM         => fl_composed_rem,
            RX_SOF_N       => fl_composed_sof_n,
            RX_SOP_N       => fl_composed_sop_n,
            RX_EOP_N       => fl_composed_eop_n,
            RX_EOF_N       => fl_composed_eof_n,
            RX_SRC_RDY_N   => fl_composed_src_rdy_n,
            RX_DST_RDY_N   => fl_composed_dst_rdy_n,
            
            -- output interface
            TX_DATA        => TX_DATA,
            TX_REM         => TX_REM,
            TX_SOF_N       => TX_SOF_N,
            TX_SOP_N       => TX_SOP_N,
            TX_EOP_N       => TX_EOP_N,
            TX_EOF_N       => TX_EOF_N,
            TX_SRC_RDY_N   => TX_SRC_RDY_N,
            TX_DST_RDY_N   => TX_DST_RDY_N
         ); 
   end generate;

   -- -------------------------------------------------------------------------
   --                        Output without FL Relay
   -- -------------------------------------------------------------------------

   noflrel_gen: if (FL_RELAY = false) generate
   begin
      TX_DATA        <= fl_composed_data;
      TX_REM         <= fl_composed_rem;
      TX_SOF_N       <= fl_composed_sof_n;
      TX_SOP_N       <= fl_composed_sop_n;
      TX_EOP_N       <= fl_composed_eop_n;
      TX_EOF_N       <= fl_composed_eof_n;
      TX_SRC_RDY_N   <= fl_composed_src_rdy_n;
   
      fl_composed_dst_rdy_n   <= TX_DST_RDY_N;
   end generate;

end architecture FL_COMPOSER_ARCH;
