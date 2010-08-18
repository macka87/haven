-- buf.vhd: Architecture of XGMII OBUF's Buf part
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use work.xgmii_obuf_pkg.all;
use work.math_pack.all;
use work.math_pack.all;
use work.fifo_pkg.all;
use work.lb_pkg.all;


-- -----------------------------------------------------------------------------
--                             Architecture
-- -----------------------------------------------------------------------------
architecture obuf_xgmii_buf_arch of obuf_xgmii_buf is

   -- Constant definition
   constant C_DREM_OUT_MAX       : integer := log2(DATA_WIDTH/8)-1;
   constant C_DFIFO_WIDTH        : integer :=
                                   DATA_WIDTH + log2(DATA_WIDTH/8) + 2;
   constant C_DATA_LSB           : integer := 0;
   constant C_DATA_MSB           : integer := DATA_WIDTH-1;
   constant C_REM_LSB            : integer := C_DATA_MSB + 1;
   constant C_REM_MSB            : integer := C_REM_LSB + C_DREM_OUT_MAX;
   constant C_SOP_POS            : integer := C_REM_MSB + 1;
   constant C_EOP_POS            : integer := C_SOP_POS + 1;

   -- addresses
   constant REG_CNT_PACKETS_ADDR_LOW   : std_logic_vector(5 downto 2) := "0000";
   constant REG_CNT_SENT_ADDR_LOW      : std_logic_vector(5 downto 2) := "0001";
   constant REG_CNT_NOTSENT_ADDR_LOW   : std_logic_vector(5 downto 2) := "0010";
   constant REG_CNT_PACKETS_ADDR_HIGH  : std_logic_vector(5 downto 2) := "0100";
   constant REG_CNT_SENT_ADDR_HIGH     : std_logic_vector(5 downto 2) := "0101";
   constant REG_CNT_NOTSENT_ADDR_HIGH  : std_logic_vector(5 downto 2) := "0110";
   constant REG_OBUF_EN_ADDR     : std_logic_vector(5 downto 2) := "1000";
   constant REG_MAC_LOW_ADDR     : std_logic_vector(5 downto 2) := "1001";
   constant REG_MAC_HIGH_ADDR    : std_logic_vector(5 downto 2) := "1010";
   constant REG_CTRL_ADDR        : std_logic_vector(5 downto 2) := "1011";
   constant REG_STATUS_ADDR      : std_logic_vector(5 downto 2) := "1100";

   -- Signals declaration
	-- asynchronous reset for FIFOs
	signal async_fifo_reset   		: std_logic;
   
   -- Data FIFO signals
   signal dfifo_overflow         : std_logic;
   signal dfifo_release          : std_logic;
   signal dfifo_rd               : std_logic;
   signal dfifo_data_in          : std_logic_vector(C_DFIFO_WIDTH-1 downto 0);
   signal dfifo_data_out         : std_logic_vector(C_DFIFO_WIDTH-1 downto 0);
   signal dfifo_empty            : std_logic;
   signal dfifo_full             : std_logic;
   signal dfifo_data_vld         : std_logic;

   -- Header/Footer FIFO signals
   signal hfifo_rd               : std_logic;
   signal hfifo_data_out         : std_logic_vector(C_FTR_MAX_BIT downto 0);
   signal hfifo_data_vld         : std_logic;

   -- Reading from FIFOs
   signal output_part_rdy        : std_logic;
   signal fsm_eop                : std_logic;
   signal fsm_frame_rdy          : std_logic;
   signal packet_start           : std_logic;
   signal packet_discarded       : std_logic;
   signal fsm_dfifo_rd           : std_logic;

   -- FL Transformer signals
   signal fltra_rx_src_rdy_n     : std_logic;
   signal fltra_rx_dst_rdy_n     : std_logic;
   signal fltra_tx_data          : std_logic_vector(63 downto 0);
   signal fltra_tx_rem           : std_logic_vector(2 downto 0);
   signal fltra_tx_sof_n         : std_logic;
   signal fltra_tx_eof_n         : std_logic;
   signal fltra_tx_src_rdy_n     : std_logic;
   signal fltra_tx_dst_rdy_n     : std_logic;

   -- FL PIPE signals
   signal flpip_tx_sof_n         : std_logic;
   signal flpip_tx_eof_n         : std_logic;
   signal flpip_tx_src_rdy_n     : std_logic;
   signal flpip_tx_dst_rdy_n     : std_logic;

   -- SW readable/writable registers
   signal reset_counters         : std_logic;
   signal reg_counters_we        : std_logic;
   signal reg_cnt_packets        : std_logic_vector(63 downto 0);
   signal reg_cnt_sent           : std_logic_vector(63 downto 0);
   signal reg_cnt_notsent        : std_logic_vector(63 downto 0);
   signal reg_obuf_en_we         : std_logic;
   signal reg_obuf_en            : std_logic;
   signal reg_mac_low_we         : std_logic;
   signal reg_mac_high_we        : std_logic;
   signal reg_mac                : std_logic_vector(47 downto 0);
   signal reg_ctrl_we            : std_logic;

   -- Decoder
   signal mx_decoder_mi_drd      : std_logic_vector(31 downto 0);
   signal reg_obuf_en_cs         : std_logic;
   signal reg_mac_low_cs         : std_logic;
   signal reg_mac_high_cs        : std_logic;
   signal reg_ctrl_cs            : std_logic;
   signal reg_status_cs          : std_logic;
   signal reg_obuf_en32          : std_logic_vector(31 downto 0);
   signal reg_mac_low32          : std_logic_vector(31 downto 0);
   signal reg_mac_high32         : std_logic_vector(31 downto 0);

   -- MI32
   signal mi_int                 : t_mi32;
   signal mi_master              : t_mi32;

   -- Counters
   signal cnt_packets            : std_logic_vector(63 downto 0);
   signal reg_cnt_packets_ce     : std_logic;
   signal cnt_sent               : std_logic_vector(63 downto 0);
   signal cnt_sent_ce            : std_logic;
   signal reg_cnt_sent_ce        : std_logic;
   signal cnt_notsent            : std_logic_vector(63 downto 0);
   signal cnt_notsent_ce         : std_logic;
   signal reg_cnt_notsent_ce     : std_logic;

begin

   assert (DATA_WIDTH >= 64)
      report "XGMII_OBUF: Buf: Bad generic DATA_WIDTH - must be at least 64."
      severity error;


   -- -------------------------------------------------------------------------
   --                           FIFOs Part
   -- -------------------------------------------------------------------------

	-- asynchronous reset for FIFOs
   async_fifo_reset <= RESET_FL or RESET_XGMII;

   -- Data FIFO ---------------------------------------------------------------
   dfifoi: entity work.asfifo_bram_release
      generic map(
         ITEMS          => DFIFO_SIZE,
         BRAM_TYPE      => 0,
         DATA_WIDTH     => C_DFIFO_WIDTH,
         STATUS_WIDTH   => 1,
         AUTO_PIPELINE  => true
      )
      port map(
         RESET          => async_fifo_reset,

         CLK_WR         => FL_CLK,
         WR             => RX_WR,
         DI             => dfifo_data_in,
         FULL           => dfifo_full,
         STATUS         => open,
         MARK           => RX_MARK,
         RELEASE        => dfifo_release,

         CLK_RD         => XGMII_CLK,
         RD             => dfifo_rd,
         DO             => dfifo_data_out,
         DO_DV          => dfifo_data_vld,
         EMPTY          => dfifo_empty
      );

   RX_DFIFO_FULL  <= dfifo_full;
   RX_DFIFO_OVF   <= dfifo_overflow;
   dfifo_overflow <= dfifo_full and dfifo_empty;
   dfifo_release  <= dfifo_overflow or (not RX_HDATA(C_FRAME_VLD_POS)
                     and RX_HFIFO_WR);

   dfifo_data_in(C_DATA_MSB downto C_DATA_LSB) <= RX_DATA;
   dfifo_data_in(C_REM_MSB  downto C_REM_LSB)  <= RX_EOP_POS;
   dfifo_data_in(C_SOP_POS)                    <= RX_SOP_N;
   dfifo_data_in(C_EOP_POS)                    <= RX_EOP_N;

   -- Header FIFO --------------------------------------------------------------
   hfifoi: entity work.fifo_async_ord
      generic map(
         MEM_TYPE       => HFIFO_MEMTYPE,
         ITEMS          => HFIFO_SIZE,
         ITEM_WIDTH     => C_FTR_MAX_BIT+1,
         PREFETCH       => true
      )
      port map(
         WR_CLK         => FL_CLK,
         WR             => RX_HFIFO_WR,
         DI             => RX_HDATA,

         RD_CLK         => XGMII_CLK,
         RD             => hfifo_rd,
         DO             => hfifo_data_out,
         DO_DV          => hfifo_data_vld,

         EMPTY          => open,
         FULL           => RX_HFIFO_FULL,
         STATUS         => open,
         RESET          => async_fifo_reset
      );

   SRC_MAC_RPLC <= hfifo_data_out(C_RPLC_SRC_MAC_POS);
   hfifo_rd <= NEXT_SRC_MAC_RPLC or packet_discarded;
   packet_discarded <= not hfifo_data_out(C_FRAME_VLD_POS) and hfifo_data_vld;

   -- -------------------------------------------------------------------------
   --                                 FSM
   -- -------------------------------------------------------------------------

   buf_fsmi: entity work.obuf_xgmii_buf_fsm
      port map(
         -- Clock signal
         CLK               => XGMII_CLK,
         -- Synchronous XGMII reset
         RESET             => RESET_XGMII,
         -- Input interface
         REG_OBUF_EN       => reg_obuf_en,
         EOP               => fsm_eop,
         FRAME_RDY         => fsm_frame_rdy,
         -- Output interface
         DFIFO_RD          => fsm_dfifo_rd
      );

   dfifo_rd       <= fsm_dfifo_rd and output_part_rdy;
   fsm_eop        <= not dfifo_data_out(C_EOP_POS) and dfifo_data_vld and
                     dfifo_rd;
   fsm_frame_rdy  <= hfifo_data_vld and hfifo_data_out(C_FRAME_VLD_POS) and
                     dfifo_data_vld;
   packet_start   <= not (fltra_rx_dst_rdy_n or fltra_rx_src_rdy_n or
                     dfifo_data_out(C_SOP_POS));

   -- -------------------------------------------------------------------------
   --                           Data transform part
   -- -------------------------------------------------------------------------

   -- Read from DFIFO only when transformer is ready
   output_part_rdy <= not fltra_rx_dst_rdy_n;

   fltrai: entity work.FL_TRANSFORMER
      generic map(
         -- FrameLink data buses width
         -- only 8, 16, 32, 64 and 128 supported
         RX_DATA_WIDTH  => DATA_WIDTH,
         TX_DATA_WIDTH  => 64
      )
      port map(
         CLK            => XGMII_CLK,
         RESET          => RESET_XGMII,

         -- RX interface
         RX_DATA        => dfifo_data_out(C_DATA_MSB downto C_DATA_LSB),
         RX_REM         => dfifo_data_out(C_REM_MSB downto C_REM_LSB),
         RX_SOF_N       => dfifo_data_out(C_SOP_POS),
         RX_EOF_N       => dfifo_data_out(C_EOP_POS),
         RX_SOP_N       => dfifo_data_out(C_SOP_POS),
         RX_EOP_N       => dfifo_data_out(C_EOP_POS),
         RX_SRC_RDY_N   => fltra_rx_src_rdy_n,
         RX_DST_RDY_N   => fltra_rx_dst_rdy_n,

         -- TX interface
         TX_DATA        => fltra_tx_data,
         TX_REM         => fltra_tx_rem,
         TX_SOF_N       => fltra_tx_sof_n,
         TX_EOF_N       => fltra_tx_eof_n,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SRC_RDY_N   => fltra_tx_src_rdy_n,
         TX_DST_RDY_N   => fltra_tx_dst_rdy_n
      );

   flpipei: entity work.FL_PIPE
      generic map(
         -- FrameLink Data Width
         DATA_WIDTH     => 64,
	 USE_OUTREG     => true
      )
      port map(
         -- Common interface 
         CLK            => XGMII_CLK,
         RESET          => RESET_XGMII,

         -- Input interface
         RX_SOF_N       => fltra_tx_sof_n,
         RX_SOP_N       => fltra_tx_sof_n,
         RX_EOP_N       => fltra_tx_eof_n,
         RX_EOF_N       => fltra_tx_eof_n,
         RX_SRC_RDY_N   => fltra_tx_src_rdy_n,
         RX_DST_RDY_N   => fltra_tx_dst_rdy_n,
         RX_DATA        => fltra_tx_data,
         RX_REM         => fltra_tx_rem,

         -- Output interface
         TX_SOF_N       => flpip_tx_sof_n,
         TX_EOP_N       => open,
         TX_SOP_N       => open,
         TX_EOF_N       => flpip_tx_eof_n,
         TX_SRC_RDY_N   => flpip_tx_src_rdy_n,
         TX_DST_RDY_N   => flpip_tx_dst_rdy_n,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_EOP_POS
      );

   -- Source of data for transformer is ready when reading from DFIFO is
   -- in progress
   fltra_rx_src_rdy_n <= not (dfifo_rd and dfifo_data_vld);

   -- Output signals
   TX_DV  <= not flpip_tx_src_rdy_n and TX_DST_RDY;
   TX_SOP <= not flpip_tx_sof_n;
   TX_EOP <= not flpip_tx_eof_n;
   flpip_tx_dst_rdy_n <= not TX_DST_RDY;

   -- -------------------------------------------------------------------------
   --                    SW readable/writable registers
   -- -------------------------------------------------------------------------

   -- register reg_cnt_packets
   reg_cnt_packetsp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (reg_counters_we = '1') then
            reg_cnt_packets <= cnt_packets;
         end if;
      end if;
   end process;

   -- register reg_cnt_sent
   reg_cnt_sentp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (reg_counters_we = '1') then
            reg_cnt_sent <= cnt_sent;
         end if;
      end if;
   end process;

   -- register reg_cnt_notsent
   reg_cnt_notsentp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (reg_counters_we = '1') then
            reg_cnt_notsent <= cnt_notsent;
         end if;
      end if;
   end process;

   -- register reg_obuf_en
   reg_obuf_enp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (RESET_XGMII = '1') then
            reg_obuf_en <= '0';
         elsif (reg_obuf_en_we = '1') then
            reg_obuf_en <= mi_int.DWR(0);
         end if;
      end if;
   end process;

   -- register reg_mac
   reg_macp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (reg_mac_low_we = '1') then
            reg_mac(31 downto 0) <= mi_int.DWR(31 downto 0);
         elsif (reg_mac_high_we = '1') then
            reg_mac(47 downto 32) <= mi_int.DWR(15 downto 0);
         end if;
      end if;
   end process;
   REG_MAC_ADDR <= reg_mac;

   -- control register
   reg_counters_wep: process(mi_int.DWR(7 downto 0), reg_ctrl_we)
   begin
      if ((mi_int.DWR(7 downto 0) = OBUFCMD_STROBE_COUNTERS) and (reg_ctrl_we = '1')) then
         reg_counters_we <= '1';
      else
         reg_counters_we <= '0';
      end if;
   end process;

   reset_countersp: process(mi_int.DWR(7 downto 0), reg_ctrl_we)
   begin
      if ((mi_int.DWR(7 downto 0) = OBUFCMD_RESET_COUNTERS) and (reg_ctrl_we = '1')) then
         reset_counters <= '1';
      else
         reset_counters <= '0';
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                               Decoder Part
   -- -------------------------------------------------------------------------

   mi_int.DRDY <= mi_int.RD;
   mi_int.ARDY <= '1';
   mi_int.DRD  <= mx_decoder_mi_drd;

   -- write part
   reg_obuf_en_we    <= reg_obuf_en_cs and mi_int.WR;
   reg_mac_low_we    <= reg_mac_low_cs and mi_int.WR;
   reg_mac_high_we   <= reg_mac_high_cs and mi_int.WR;
   reg_ctrl_we       <= reg_ctrl_cs and mi_int.WR;

   -- Set CS signals according to mi_int.ADDR
   chip_selectp: process(mi_int.ADDR(5 downto 2))
   begin
      reg_obuf_en_cs <= '0';
      reg_mac_low_cs <= '0';
      reg_mac_high_cs <= '0';
      reg_ctrl_cs <= '0';

      case (mi_int.ADDR(5 downto 2)) is
         when REG_OBUF_EN_ADDR      => reg_obuf_en_cs       <= '1';
         when REG_MAC_LOW_ADDR      => reg_mac_low_cs       <= '1';
         when REG_MAC_HIGH_ADDR     => reg_mac_high_cs      <= '1';
         when REG_CTRL_ADDR         => reg_ctrl_cs          <= '1';
         when others =>
      end case;
   end process;

   -- Reading Part
   -- 32bit-wide signals
   reg_obuf_en32 <= (31 downto 1 => '0') & reg_obuf_en;
   reg_mac_low32 <= reg_mac(31 downto 0);
   reg_mac_high32 <= (31 downto 16 => '0') & reg_mac(47 downto 32);

   -- Output register multiplexer
   mx_decoder_mi_drdp: process(mi_int.ADDR(5 downto 2), reg_cnt_packets,
      reg_cnt_sent, reg_cnt_notsent, reg_obuf_en32, reg_mac_low32,
      reg_mac_high32)
   begin
      case (mi_int.ADDR(5 downto 2)) is
         when REG_CNT_PACKETS_ADDR_LOW =>
            mx_decoder_mi_drd <= reg_cnt_packets(31 downto 0);
         when REG_CNT_SENT_ADDR_LOW =>
            mx_decoder_mi_drd <= reg_cnt_sent(31 downto 0);
         when REG_CNT_NOTSENT_ADDR_LOW =>
            mx_decoder_mi_drd <= reg_cnt_notsent(31 downto 0);
         when REG_CNT_PACKETS_ADDR_HIGH =>
            mx_decoder_mi_drd <= reg_cnt_packets(63 downto 32);
         when REG_CNT_SENT_ADDR_HIGH =>
            mx_decoder_mi_drd <= reg_cnt_sent(63 downto 32);
         when REG_CNT_NOTSENT_ADDR_HIGH =>
            mx_decoder_mi_drd <= reg_cnt_notsent(63 downto 32);
         when REG_OBUF_EN_ADDR =>
            mx_decoder_mi_drd <= reg_obuf_en32;
         when REG_MAC_LOW_ADDR =>
            mx_decoder_mi_drd <= reg_mac_low32;
         when REG_MAC_HIGH_ADDR =>
            mx_decoder_mi_drd <= reg_mac_high32;
         when REG_STATUS_ADDR =>
            mx_decoder_mi_drd <= (5 downto 4 => '1', others => '0');
         when others =>
            mx_decoder_mi_drd <= (others => '0');
      end case;
   end process;

   -- -------------------------------------------------------------------------
   --                       Asynchronous MI32 connection
   -- -------------------------------------------------------------------------

   -- Asynchronous MI32 interface
   mi32_asynci: entity work.mi32_async
      port map(
         RESET             => RESET_MI,
         CLK_M             => MI_CLK,
         MI_M              => mi_master,
         CLK_S             => XGMII_CLK,
         MI_S              => mi_int
      );

   mi_master.DWR <= MI_DWR;
   mi_master.ADDR <= MI_ADDR;
   mi_master.RD <= MI_RD;
   mi_master.WR <= MI_WR;
   mi_master.BE <= MI_BE;
   MI_DRD <= mi_master.DRD;
   MI_ARDY <= mi_master.ARDY;
   MI_DRDY <= mi_master.DRDY;

   -- -------------------------------------------------------------------------
   --                                Counters
   -- -------------------------------------------------------------------------

   cnt_sent_ce <= packet_start and dfifo_rd;
   cnt_notsent_ce <= packet_discarded;

   -- Registers to improve performance
   process(XGMII_CLK)
   begin
      if (XGMII_CLK'event and XGMII_CLK='1') then
         reg_cnt_packets_ce <= cnt_sent_ce or cnt_notsent_ce;
         reg_cnt_sent_ce <= cnt_sent_ce;
         reg_cnt_notsent_ce <= cnt_notsent_ce;
      end if;
   end process;

   -- cnt_packets counter
   cnt_packetsp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (RESET_XGMII = '1' or reset_counters = '1') then
            cnt_packets <= (others => '0');
         elsif (reg_cnt_packets_ce = '1') then
            cnt_packets <= cnt_packets + 1;
         end if;
      end if;
   end process;

   -- cnt_sent counter
   cnt_sentp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (RESET_XGMII = '1' or reset_counters = '1') then
            cnt_sent <= (others => '0');
         elsif (reg_cnt_sent_ce = '1') then
            cnt_sent <= cnt_sent + 1;
         end if;
      end if;
   end process;

   -- cnt_notsent counter
   cnt_notsentp: process(XGMII_CLK)
   begin
      if (XGMII_CLK'event AND XGMII_CLK = '1') then
         if (RESET_XGMII = '1' or reset_counters = '1') then
            cnt_notsent <= (others => '0');
         elsif (reg_cnt_notsent_ce = '1') then
            cnt_notsent <= cnt_notsent + 1;
         end if;
      end if;
   end process;

end architecture obuf_xgmii_buf_arch;
