-- buf.vhd: Buffer component of XGMII IBUF
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
use work.ibuf_pkg.all;
use work.fifo_pkg.all;
use work.ibuf_general_pkg.all;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture XGMII_IBUF_BUF_ARCH of XGMII_IBUF_BUF is

   -- Constants definition
   constant C_DREM_OUT_MAX       : integer := log2(FL_WIDTH_TX/8)-1;
   constant C_OFIFO_WIDTH        : integer
                           := FL_WIDTH_TX + log2(FL_WIDTH_TX/8) + 2;
   constant C_DATA_LSB           : integer := 0;
   constant C_DATA_MSB           : integer := FL_WIDTH_TX-1;
   constant C_REM_LSB            : integer := C_DATA_MSB + 1;
   constant C_REM_MSB            : integer := C_REM_LSB + C_DREM_OUT_MAX;
   constant C_SOP_POS            : integer := C_REM_MSB + 1;
   constant C_EOP_POS            : integer := C_SOP_POS + 1;

   -- Signal declaration
   -- Valid statistic data
   signal stats_vector           : std_logic_vector(5 downto 1);
   -- Error mask
   signal error_mask             : std_logic_vector(5 downto 1);
   -- Masked statistic data
   signal stats_vector_masked    : std_logic_vector(5 downto 1);
   signal xgmii_err_masked       : std_logic;
   -- Error signals
   signal xgmii_err              : std_logic;
   signal stats_err              : std_logic;
   -- Register to remember XGMII error in the frame
   signal reg_xgmii_err          : std_logic;
   signal reg_xgmii_err_sync_rst : std_logic;
   -- Register with information whether discard because of statistic
   signal reg_stat_discard_in    : std_logic;
   signal reg_stat_discard_we    : std_logic;
   signal reg_stat_discard       : std_logic;

   -- Registers for input data
   signal reg_data_pipe          : std_logic_vector(63 downto 0);
   signal reg_sop_pipe           : std_logic;
   signal reg_eop_pipe           : std_logic;
   signal reg_eop_pos_pipe       : std_logic_vector(2 downto 0);
   signal reg_stats              : t_stats;
   signal reg_xgmii_err_stat     : std_logic;

   -- FSM before FL Transformer
   signal fltrafsm_discarded     : std_logic;
   signal fltrafsm_bo            : std_logic;

   -- FL Transformer input
   signal fltra_data_rx          : std_logic_vector(63 downto 0);
   signal fltra_sop_rx_n         : std_logic;
   signal fltra_eop_rx_n         : std_logic;
   signal fltra_sof_rx_n         : std_logic;
   signal fltra_eof_rx_n         : std_logic;
   signal fltra_rem_rx           : std_logic_vector(2 downto 0);
   signal fltra_src_rdy_rx_n     : std_logic;
   signal fltra_dst_rdy_rx_n     : std_logic;

   -- FL Transformer output
   signal fltra_data_tx          : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal fltra_sop_tx_n         : std_logic;
   signal fltra_eop_tx_n         : std_logic;
   signal fltra_rem_tx           : std_logic_vector(C_DREM_OUT_MAX downto 0);
   signal fltra_src_rdy_tx_n     : std_logic;

   -- Registers between FL Transformer and FSM
   signal reg_fsm_data_rx        : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal reg_fsm_rem_rx         : std_logic_vector(C_DREM_OUT_MAX downto 0);
   signal reg_fsm_sop_rx_n       : std_logic;
   signal reg_fsm_eop_rx_n_in    : std_logic;
   signal reg_fsm_eop_rx_n       : std_logic;
   signal reg_fsm_discard_rx     : std_logic;
   signal reg_fsm_rx_active      : std_logic;
   signal reg_stats_tra          : t_stats;
   signal reg_xgmii_err_stat_tra : std_logic;

   -- Signals incoming to the FSM Part
   signal fsm_data_rx            : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal fsm_sop_rx_n           : std_logic;
   signal fsm_eop_rx_n           : std_logic;
   signal fsm_rem_rx             : std_logic_vector(C_DREM_OUT_MAX downto 0);
   signal fsm_discard_rx         : std_logic;
   signal fsm_active             : std_logic;
   signal fsm_dfifo_full         : std_logic;

   -- Signals outgoing from FSM Part
   signal fsm_dfifo_wr           : std_logic;
   signal fsm_pacodag_ovf        : std_logic;
   signal fsm_dfifo_ovf          : std_logic;

   -- Register for start of regular data of packet
   signal reg_rsop_n             : std_logic;

   -- Data FIFO signals
   signal dfifo_data_in          : std_logic_vector(C_OFIFO_WIDTH-1 downto 0);
   signal dfifo_data_out         : std_logic_vector(C_OFIFO_WIDTH-1 downto 0);
   signal dfifo_full             : std_logic;
   signal dfifo_empty            : std_logic;
   signal dfifo_release          : std_logic;
   signal dfifo_mark             : std_logic;
   signal dfifo_wr               : std_logic;
   signal dfifo_rd               : std_logic;
   signal dfifo_data_vld         : std_logic;

   -- Header/Footer FIFO signals
   signal hfifo_data_in          : std_logic_vector(C_OFIFO_WIDTH-1 downto 0);
   signal hfifo_data_out         : std_logic_vector(C_OFIFO_WIDTH-1 downto 0);
   signal hfifo_full             : std_logic;
   signal hfifo_empty            : std_logic;
   signal hfifo_wr               : std_logic;
   signal hfifo_rd               : std_logic;
   signal hfifo_data_vld         : std_logic;

   -- Counters
   signal cnt_trfc               : std_logic_vector(63 downto 0);
   signal cnt_trfc_ce            : std_logic;
   signal cnt_trfc_ld            : std_logic;
   signal cnt_cfc                : std_logic_vector(63 downto 0);
   signal cnt_cfc_ce             : std_logic;
   signal cnt_cfc_ld             : std_logic;
   signal cnt_dfc                : std_logic_vector(63 downto 0);
   signal cnt_dfc_ce             : std_logic;
   signal cnt_dfc_ld             : std_logic;
   signal cnt_bodfc              : std_logic_vector(63 downto 0);
   signal cnt_bodfc_ce           : std_logic;
   signal cnt_bodfc_ld           : std_logic;

begin

   assert (FL_WIDTH_TX >= 64)
      report "XGMII_IBUF: Buf: Bad generic FL_WIDTH_TX - must be at least 64."
      severity error;


   -- -------------------------------------------------------------------------
   --                             Statistics
   -- -------------------------------------------------------------------------

   stats_vector(1) <= STATS.CRC_ERR;
   stats_vector(2) <= STATS.MINTU_ERR;
   stats_vector(3) <= STATS.MTU_ERR;
   stats_vector(4) <= STATS.MAC_ERR;
   stats_vector(5) <= STATS.SAU_ERR and STATS.SAU_ERR_VLD;

   error_mask           <= '1' & MI2BUF.ERROR_MASK(4 downto 1);
   stats_vector_masked  <= stats_vector and error_mask;

   -- Figure out if there are at least one statistic active
   stats_errp: process(stats_vector_masked)
   begin
      if (stats_vector_masked /= 0) then
         stats_err <= '1';
      else
         stats_err <= '0';
      end if;
   end process;

   -- register reg_xgmii_err
   reg_xgmii_err_sync_rst <= RX_SOP;
   reg_xgmii_errp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_xgmii_err <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_xgmii_err_sync_rst = '1') then
            reg_xgmii_err <= RX_ERR;
         elsif (xgmii_err = '1') then
            reg_xgmii_err <= '1';
         end if;
      end if;
   end process;

   xgmii_err           <= reg_xgmii_err or RX_ERR;
   xgmii_err_masked    <= xgmii_err and MI2BUF.ERROR_MASK(0);
   reg_stat_discard_in <= xgmii_err_masked or stats_err;

   -- register reg_stat_discard
   reg_stat_discard_we <= RX_EOP;
   reg_stat_discardp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_stat_discard <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_stat_discard_we = '1') then
            reg_stat_discard <= reg_stat_discard_in;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                             Input registers
   -- -------------------------------------------------------------------------
 
   input_registersp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_sop_pipe      <= '0';
         reg_eop_pipe      <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_data_pipe     <= RX_DATA;
         reg_sop_pipe      <= RX_SOP;
         reg_eop_pipe      <= RX_EOP;
         reg_eop_pos_pipe  <= RX_EOP_POS;
      end if;
   end process;

   -- Register to put preamble away (also inverts SOP)
   -- register reg_rsop_n
   reg_rsop_np: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_rsop_n <= '1';
      elsif (CLK'event AND CLK = '1') then
         reg_rsop_n <= not reg_sop_pipe;
      end if;
   end process;

   -- register reg_stats
   reg_statsp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_stats <= STATS;
      end if;
   end process;

   -- register reg_xgmii_err_stat
   reg_xgmii_err_statp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         reg_xgmii_err_stat <= xgmii_err;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                       Transform to output width
   -- -------------------------------------------------------------------------

   -- Generate this part only if FL_WIDTH_TX /= 64

   fltra_gen: if (FL_WIDTH_TX > 64) generate
   begin
      
      -- Input signals
      fltra_data_rx     <= reg_data_pipe;
      fltra_sop_rx_n    <= reg_rsop_n;
      fltra_eop_rx_n    <= not reg_eop_pipe;
      fltra_sof_rx_n    <= fltra_sop_rx_n;
      fltra_eof_rx_n    <= fltra_eop_rx_n;
      fltra_rem_rx      <= reg_eop_pos_pipe;
   
      -- Creates SRC_RDY signal for FL Transformer
     buf_fl_src_rdy_fsmi: entity work.buf_fl_src_rdy_fsm
        port map (
            CLK               => CLK,
            RESET             => RESET,
            
            RX_SOP_N          => fltra_sop_rx_n,
            RX_EOP_N          => fltra_eop_rx_n,
            TX_DST_RDY_N      => fltra_dst_rdy_rx_n,
      
            TX_SRC_RDY_N      => fltra_src_rdy_rx_n,
            FRAME_DISCARDED   => fltrafsm_discarded,
            BUFFER_OVERFLOW   => fltrafsm_bo
         ); 
    
      -- FL Transformer
      fltrai: entity work.fl_transformer_async_rst
         generic map(
            RX_DATA_WIDTH  => 64,
            TX_DATA_WIDTH  => FL_WIDTH_TX
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
      
            RX_DATA        => fltra_data_rx,
            RX_REM         => fltra_rem_rx,
            RX_SOF_N       => fltra_sof_rx_n,
            RX_EOF_N       => fltra_eof_rx_n,
            RX_SOP_N       => fltra_sop_rx_n,
            RX_EOP_N       => fltra_eop_rx_n,
            RX_SRC_RDY_N   => fltra_src_rdy_rx_n,
            RX_DST_RDY_N   => fltra_dst_rdy_rx_n,
      
            TX_DATA        => fltra_data_tx,
            TX_REM         => fltra_rem_tx,
            TX_SOF_N       => open,
            TX_EOF_N       => open,
            TX_SOP_N       => fltra_sop_tx_n,
            TX_EOP_N       => fltra_eop_tx_n,
            TX_SRC_RDY_N   => fltra_src_rdy_tx_n,
            TX_DST_RDY_N   => '0'
         );
   
      -- Registers to improve performance -------------------------------------
      -- register reg_fsm_data_rx
      reg_fsm_data_rxp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            reg_fsm_data_rx <= fltra_data_tx;
         end if;
      end process;

      -- register reg_fsm_rem_rx
      reg_fsm_rem_rxp: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            reg_fsm_rem_rx <= fltra_rem_tx;
         end if;
      end process;

      -- register reg_fsm_sop_rx_n
      reg_fsm_sop_rx_np: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_fsm_sop_rx_n <= '1';
         elsif (CLK'event AND CLK = '1') then
            reg_fsm_sop_rx_n <= fltra_sop_tx_n or fltra_src_rdy_tx_n;
         end if;
      end process;

      reg_fsm_eop_rx_n_in <= fltra_eop_tx_n or fltra_src_rdy_tx_n;
      -- register reg_fsm_eop_rx_n
      reg_fsm_eop_rx_np: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_fsm_eop_rx_n <= '1';
         elsif (CLK'event AND CLK = '1') then
            reg_fsm_eop_rx_n <= reg_fsm_eop_rx_n_in;
         end if;
      end process;

      -- register reg_fsm_discard_rx
      reg_fsm_discard_rxp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_fsm_discard_rx <= '0';
         elsif (CLK'event AND CLK = '1') then
            reg_fsm_discard_rx <= reg_stat_discard and not reg_fsm_eop_rx_n_in;
         end if;
      end process;

      -- register reg_fsm_rx_active
      reg_fsm_rx_activep: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_fsm_rx_active <= '0';
         elsif (CLK'event AND CLK = '1') then
            reg_fsm_rx_active <= not fltra_src_rdy_tx_n;
         end if;
      end process;

      -- Registers connected to FSM part input
      fsm_data_rx    <= reg_fsm_data_rx;
      fsm_rem_rx     <= reg_fsm_rem_rx;
      fsm_sop_rx_n   <= reg_fsm_sop_rx_n;
      fsm_eop_rx_n   <= reg_fsm_eop_rx_n;
      fsm_discard_rx <= reg_fsm_discard_rx;
      fsm_active     <= reg_fsm_rx_active;
      fsm_dfifo_full <= dfifo_full and reg_fsm_rx_active;

      -- Statistic data of actual frame --------------------------------------
      -- register reg_stats_tra
      reg_stats_trap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            reg_stats_tra <= reg_stats;
         end if;
      end process;
      
      -- register reg_xgmii_err_stat
      reg_xgmii_err_stat_trap: process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            reg_xgmii_err_stat_tra <= reg_xgmii_err_stat;
         end if;
      end process;

      STATS_OUT.PAYLOAD_LEN      <= reg_stats_tra.FRAME_LEN;
      STATS_OUT.FRAME_ERROR      <= reg_xgmii_err_stat_tra;
      STATS_OUT.CRC_CHECK_FAILED <= reg_stats_tra.CRC_ERR;
      STATS_OUT.MAC_CHECK_FAILED <= reg_stats_tra.MAC_ERR;
      STATS_OUT.LEN_BELOW_MIN    <= reg_stats_tra.MINTU_ERR;
      STATS_OUT.LEN_OVER_MTU     <= reg_stats_tra.MTU_ERR;
      STATS_OUT_VLD              <= not reg_fsm_eop_rx_n;

   end generate fltra_gen;

   -- -------------------------------------------------------------------------
   --                     Create FL without Transformer
   -- -------------------------------------------------------------------------

   fllight_gen: if (FL_WIDTH_TX = 64) generate
   begin

      fsm_data_rx    <= reg_data_pipe;
      fsm_rem_rx     <= reg_eop_pos_pipe;
      fsm_sop_rx_n   <= reg_rsop_n;
      fsm_eop_rx_n   <= not reg_eop_pipe;
      fsm_discard_rx <= reg_stat_discard and reg_eop_pipe;
      fsm_active     <= '1';
      fsm_dfifo_full <= dfifo_full;

      fltrafsm_discarded   <= '0';
      fltrafsm_bo          <= '0';

      -- Map output statistic to reg_stats
      STATS_OUT.PAYLOAD_LEN      <= reg_stats.FRAME_LEN;
      STATS_OUT.FRAME_ERROR      <= reg_xgmii_err_stat;
      STATS_OUT.CRC_CHECK_FAILED <= reg_stats.CRC_ERR;
      STATS_OUT.MAC_CHECK_FAILED <= reg_stats.MAC_ERR;
      STATS_OUT.LEN_BELOW_MIN    <= reg_stats.MINTU_ERR;
      STATS_OUT.LEN_OVER_MTU     <= reg_stats.MTU_ERR;
      STATS_OUT_VLD  <= reg_eop_pipe;

   end generate fllight_gen;

   -- -------------------------------------------------------------------------
   --                             FSM Part
   -- -------------------------------------------------------------------------

   fsmi: entity work.buf_fsm
      port map(
         CLK               => CLK,
         RESET             => RESET,

         SOP_RX_N          => fsm_sop_rx_n,
         EOP_RX_N          => fsm_eop_rx_n,
         PACODAG_RDY       => CTRL_RDY,
         DISCARD_RX        => fsm_discard_rx,
         DFIFO_FULL        => fsm_dfifo_full,
         IBUF_EN           => MI2BUF.IBUF_EN,

         PACODAG_REQ       => CTRL_REQ,
         PACODAG_SEND      => CTRL_SEND,
         PACODAG_RELEASE   => CTRL_RELEASE,
         DFIFO_RELEASE     => dfifo_release,
         DFIFO_MARK        => dfifo_mark,
         DFIFO_WR          => fsm_dfifo_wr,
         PACODAG_OVF       => fsm_pacodag_ovf,
         DFIFO_OVF         => fsm_dfifo_ovf,

         STATUS_DEBUG      => BUF2MI.STATUS(C_FSM_STATUS_DEBUG_H
                                          downto C_FSM_STATUS_DEBUG_L),

         CFC               => cnt_cfc_ce,
         DFC               => cnt_dfc_ce,
         BODFC             => cnt_bodfc_ce

      );

   dfifo_wr <= fsm_dfifo_wr and fsm_active;

   BUF2MI.STATUS(C_DFIFO_OVF_POS) <= fsm_dfifo_ovf;
   BUF2MI.STATUS(C_PACODAG_OVF_POS) <= fsm_pacodag_ovf;
   BUF2MI.STATUS(C_CTRL_RDY_POS) <= CTRL_RDY;

   -- -------------------------------------------------------------------------
   --                           FIFOs Part
   -- -------------------------------------------------------------------------

   -- Data FIFO ---------------------------------------------------------------
   dfifo_data_in(C_DATA_MSB downto C_DATA_LSB) <= fsm_data_rx;
   dfifo_data_in(C_REM_MSB  downto C_REM_LSB)  <= fsm_rem_rx;
   dfifo_data_in(C_SOP_POS)                    <= fsm_sop_rx_n;
   dfifo_data_in(C_EOP_POS)                    <= fsm_eop_rx_n;

   dfifo_rd       <= not TX_DST_RDY_N;

   TX_DATA        <= dfifo_data_out(C_DATA_MSB downto C_DATA_LSB);
   TX_REM         <= dfifo_data_out(C_REM_MSB downto C_REM_LSB);
   TX_SOP_N       <= dfifo_data_out(C_SOP_POS);
   TX_EOP_N       <= dfifo_data_out(C_EOP_POS);
   TX_SRC_RDY_N   <= not dfifo_data_vld;

   dfifoi: entity work.asfifo_bram_release
      generic map(
         ITEMS          => DFIFO_SIZE,
         BRAM_TYPE      => 0,
         DATA_WIDTH     => C_OFIFO_WIDTH,
         STATUS_WIDTH   => 1,
         AUTO_PIPELINE  => true
      )
      port map(
         RESET          => RESET,

         CLK_WR         => CLK,
         WR             => dfifo_wr,
         DI             => dfifo_data_in,
         FULL           => dfifo_full,
         STATUS         => open,
         MARK           => dfifo_mark,
         RELEASE        => dfifo_release,

         CLK_RD         => FL_CLK,
         RD             => dfifo_rd,
         DO             => dfifo_data_out,
         DO_DV          => dfifo_data_vld,
         EMPTY          => dfifo_empty
      );

   BUF2MI.STATUS(C_DFIFO_FULL_POS) <= dfifo_full;
   BUF2MI.STATUS(C_DFIFO_EMPTY_POS) <= dfifo_empty;
   BUF2MI.STATUS(C_DFIFO_WR_POS) <= dfifo_wr;
   BUF2MI.STATUS(C_DFIFO_RD_POS) <= dfifo_rd;
   BUF2MI.STATUS(C_DFIFO_DO_DV_POS) <= dfifo_data_vld;

   -- Header/Footer FIFO ------------------------------------------------------
   hfifo_data_in(C_DATA_MSB downto C_DATA_LSB) <= CTRL_DATA;
   hfifo_data_in(C_REM_MSB  downto C_REM_LSB)  <= CTRL_REM;
   hfifo_data_in(C_SOP_POS)                    <= CTRL_SOP_N;
   hfifo_data_in(C_EOP_POS)                    <= CTRL_EOP_N;

   hfifo_rd       <= not TX_HDST_RDY_N and hfifo_data_vld;
   hfifo_wr       <= not (hfifo_full or CTRL_SRC_RDY_N);

   TX_HDATA       <= hfifo_data_out(C_DATA_MSB downto C_DATA_LSB);
   TX_HREM        <= hfifo_data_out(C_REM_MSB downto C_REM_LSB);
   TX_HSOP_N      <= hfifo_data_out(C_SOP_POS);
   TX_HEOP_N      <= hfifo_data_out(C_EOP_POS);
   TX_HSRC_RDY_N  <= not hfifo_data_vld;

   -- Important because of the removal of the ASFIFO from the
   assert (HFIFO_MEMTYPE = BRAM)
      report "XGMII_IBUF: Buf: Not supported hfifo memtype selected, supported value is: BRAM"
      severity error;


   hfifoi: entity work.asfifo_bram
      generic map(
         --MEM_TYPE       => HFIFO_MEMTYPE,
         ITEMS          => HFIFO_SIZE,
         DATA_WIDTH     => C_OFIFO_WIDTH,
         STATUS_WIDTH   => 2,
         AUTO_PIPELINE  => true
      )
      port map(
         CLK_WR         => CLK,
         WR             => hfifo_wr,
         DI             => hfifo_data_in,

         CLK_RD         => FL_CLK,
         RD             => hfifo_rd,
         DO             => hfifo_data_out,
         DO_DV          => hfifo_data_vld,

         EMPTY          => hfifo_empty,
         FULL           => hfifo_full,
         STATUS         => open,
         RESET          => RESET
      );

   CTRL_DST_RDY_N <= hfifo_full;

   BUF2MI.STATUS(C_HFIFO_FULL_POS) <= hfifo_full;
   BUF2MI.STATUS(C_HFIFO_EMPTY_POS) <= hfifo_empty;
   BUF2MI.STATUS(C_HFIFO_WR_POS) <= hfifo_wr;
   BUF2MI.STATUS(C_HFIFO_RD_POS) <= hfifo_rd;
   BUF2MI.STATUS(C_HFIFO_DO_DV_POS) <= hfifo_data_vld;


   -- -------------------------------------------------------------------------
   --                               Counters
   -- -------------------------------------------------------------------------

   -- Total received frames counter
   cnt_trfc_ce <= cnt_cfc_ce or cnt_dfc_ce;
   cnt_trfcp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_trfc <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_trfc_ld = '1') then
            cnt_trfc <= (others => '0');
         elsif (cnt_trfc_ce = '1') then
            cnt_trfc <= cnt_trfc + 1;
         end if;
      end if;
   end process;

   -- Correct frames counter
   cnt_cfcp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_cfc <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_cfc_ld = '1') then
            cnt_cfc <= (others => '0');
         elsif (cnt_cfc_ce = '1') then
            cnt_cfc <= cnt_cfc + 1;
         end if;
      end if;
   end process;

   -- Discarded frames counter
   cnt_dfcp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_dfc <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_dfc_ld = '1') then
            cnt_dfc <= (others => '0');
         elsif (cnt_dfc_ce = '1') then
            cnt_dfc <= cnt_dfc + 1;
         end if;
      end if;
   end process;

   -- Counter of frames discarded due to buffer overflow
   cnt_bodfcp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_bodfc <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_bodfc_ld = '1') then
            cnt_bodfc <= (others => '0');
         elsif (cnt_bodfc_ce = '1') then
            cnt_bodfc <= cnt_bodfc + 1;
         end if;
      end if;
   end process;

   cnt_trfc_ld    <= MI2BUF.CNT_RESET;
   cnt_cfc_ld     <= MI2BUF.CNT_RESET;
   cnt_dfc_ld     <= MI2BUF.CNT_RESET;
   cnt_bodfc_ld   <= MI2BUF.CNT_RESET;

   BUF2MI.TRFC    <= cnt_trfc;
   BUF2MI.CFC     <= cnt_cfc;
   BUF2MI.DFC     <= cnt_dfc;
   BUF2MI.BODFC   <= cnt_bodfc;

   BUF2MI.STATUS(C_FR_DISCARDED_POS)   <= fltrafsm_discarded;
   BUF2MI.STATUS(C_BUFFER_OVF_POS)     <= fltrafsm_bo;


end architecture XGMII_IBUF_BUF_ARCH;
