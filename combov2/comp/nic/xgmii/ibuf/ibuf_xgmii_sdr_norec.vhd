-- ibuf_xgmii_sdr_norec.vhd: XGMII SDR Input Buffer (without inout records)
-- Copyright (C) 2008 CESNET
-- Author(s): Polcak Libor <polcak_l@liberouter.org>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.lb_pkg.all;
use work.ibuf_pkg.all;
use work.xgmii_pkg.all;
use work.fifo_pkg.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture ibuf_xgmii_sdr_norec_arch of ibuf_xgmii_sdr_norec is

   -- Align input
   signal rxd_align        : std_logic_vector(63 downto 0);
   signal rxc_align        : std_logic_vector(7 downto 0);

   -- Aligned SDR XGMII protocol
   signal rxd_aligned      : std_logic_vector(63 downto 0);
   signal rxc_aligned      : std_logic_vector(7 downto 0);
   signal sop_aligned      : std_logic;

   -- Decoded Aligned SDR XGMII protocol
   signal dec_data         : std_logic_vector(63 downto 0);
   signal dec_sop          : std_logic;
   signal dec_eop          : std_logic;
   signal dec_eop_pos      : std_logic_vector(2 downto 0);
   signal dec_err          : std_logic;

   -- Check output signals to Buf
   signal check_data       : std_logic_vector(63 downto 0);
   signal check_sop        : std_logic;
   signal check_eop        : std_logic;
   signal check_eop_pos    : std_logic_vector(2 downto 0);
   signal check_err        : std_logic;
   signal check_stats      : t_stats;

   -- CAM signals
   signal cam_data          : std_logic_vector(63 downto 0);
   signal cam_match_en      : std_logic;
   signal cam_match_rst     : std_logic;
   signal cam_match_bus     : std_logic_vector(MACS-1 downto 0);
   signal cam_match_bus_vld : std_logic;

   -- Buf signals
   signal buf_data         : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal buf_rem        	: std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal buf_sop_n        : std_logic;
   signal buf_eop_n        : std_logic;
   signal buf_src_rdy_n    : std_logic;
   signal buf_dst_rdy_n    : std_logic;

   signal buf_hdata        : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal buf_hrem         : std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal buf_hsop_n       : std_logic;
   signal buf_heop_n       : std_logic;
   signal buf_hsrc_rdy_n   : std_logic;
   signal buf_hdst_rdy_n   : std_logic;

   signal reg_linkup       : std_logic;
   signal reg_incoming_pckt: std_logic;
   signal input_error_vec  : std_logic_vector(7 downto 0);
   signal input_error      : std_logic;
   signal seq_link_down    : std_logic_vector(1 downto 0);
   signal set_link_down    : std_logic;
   signal cnt_error        : std_logic_vector(CNT_ERROR_SIZE-1 downto 0);

   signal frame_receivedi  : std_logic;
   signal frame_discardedi : std_logic;
   signal buffer_ovfi      : std_logic;

   signal composer_fifo_sel: std_logic;

   -- Records from/to MI Int
   signal mi2check         : t_mi2check;
   signal mi2buf           : t_mi2buf;
   signal buf2mi           : t_buf2mi;

begin

   -- -------------------------------------------------------------------------
   --                   Deal with possible input errors
   -- -------------------------------------------------------------------------

   -- For each input line find out if it carries error command
   error_gen: for i in 0 to 7 generate
      input_errorp: process(XGMII_SDR_RXC(i), XGMII_SDR_RXD((i+1)*8-1 downto i*8))
      begin
         if (XGMII_SDR_RXC(i) = '1' AND
               XGMII_SDR_RXD((i+1)*8-1 downto i*8) = C_XGMII_ERROR) then
            input_error_vec(i) <= '1';
         else
            input_error_vec(i) <= '0';
         end if;
      end process;
   end generate error_gen;

   -- Find out if any input line carries error command
   gen_orp : process(input_error_vec)
      variable or_int : std_logic;
   begin
      or_int := '0';

      for k in 0 to input_error_vec'length -1 loop
         or_int := or_int or input_error_vec(k);
      end loop;

      input_error <= or_int;
   end process;

   -- Comparators that search for sequence link down
   seq_link_down_cmp0: process(XGMII_SDR_RXD, XGMII_SDR_RXC)
   begin
      if ((XGMII_SDR_RXD(31 downto 0) = C_SEQ_LINK_DOWN_D) AND
            (XGMII_SDR_RXC(3 downto 0) = C_SEQ_LINK_DOWN_C)) then
         seq_link_down(0) <= '1';
      else
         seq_link_down(0) <= '0';
      end if;
   end process;
   seq_link_down_cmp1: process(XGMII_SDR_RXD, XGMII_SDR_RXC)
   begin
      if ((XGMII_SDR_RXD(63 downto 32) = C_SEQ_LINK_DOWN_D) AND
            (XGMII_SDR_RXC(7 downto 4) = C_SEQ_LINK_DOWN_C)) then
         seq_link_down(1) <= '1';
      else
         seq_link_down(1) <= '0';
      end if;
   end process;

   set_link_down <= input_error or seq_link_down(0) or seq_link_down(1);

   -- Counter that determines if the link is in the correct state
   cnt_errorp: process(CLK_INT, RESET)
   begin
      if RESET = '1' then
         cnt_error <= (others => '1');
      elsif (CLK_INT'event and CLK_INT = '1') then
         if (set_link_down = '1') then
            cnt_error <= (others => '1');
         elsif (cnt_error /= 0) then
            cnt_error <= cnt_error - 1;
         end if;
      end if;
   end process;

   -- Link is up
   reg_linkupp: process(CLK_INT, RESET)
   begin
      if (RESET = '1') then
         reg_linkup <= '0';
      elsif (CLK_INT'event and CLK_INT = '1') then
         if ((set_link_down = '0') and (cnt_error = 0)) then
            reg_linkup <= '1';
         else
            reg_linkup <= '0';
         end if;
      end if;
   end process;

   -- If the link is not in the up state send idles to the core
   mx_align_inputp: process(XGMII_SDR_RXD, XGMII_SDR_RXC, reg_linkup)
   begin
      if (reg_linkup = '1') then
         rxd_align <= XGMII_SDR_RXD;
         rxc_align <= XGMII_SDR_RXC;
      else
         rxd_align <= C_XGMII_IDLE_WORD64;
         rxc_align <= (others => '1');
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                   IBUF Interface
   -- -------------------------------------------------------------------------

   -- IBUF core clock for external components
   CTRL_CLK       <= CLK_INT;
   CTRL_RESET     <= RESET;
   SAU_CLK        <= CLK_INT;
   SAU_RESET      <= RESET;
   LINK_UP        <= reg_linkup;
   INCOMING_PCKT  <= reg_incoming_pckt;

   -- -------------------------------------------------------------------------
   --                      Align Part
   -- -------------------------------------------------------------------------

   -- Align instantion
   ALIGNi: entity work.align
   port map(
      CLK            => CLK_INT,
      RESET          => RESET,

      RXD            => rxd_align,
      RXC            => rxc_align,

      RXD_ALIGNED    => rxd_aligned,
      RXC_ALIGNED    => rxc_aligned,
      SOP_ALIGNED 	=> sop_aligned
   );

   -- -------------------------------------------------------------------------
   --                     XGMII Dec Part
   -- -------------------------------------------------------------------------

   -- XGMII_DEC instantion
   XGMII_DECi: entity work.xgmii_dec
   port map(
      CLK            => CLK_INT,
      RESET          => RESET,

      RXD_ALIGNED		=> rxd_aligned,
      RXC_ALIGNED    => rxc_aligned,
      SOP_ALIGNED    => sop_aligned,

      DATA           => dec_data,
      SOP            => dec_sop,
      EOP            => dec_eop,
      EOP_POS        => dec_eop_pos,
      ERR            => dec_err
   );

   reg_incoming_pcktp: process(RESET, CLK_INT)
   begin
      if (RESET = '1') then
         reg_incoming_pckt <= '0';
      elsif (CLK_INT'event and CLK_INT = '1') then
         if dec_eop = '1' then
            reg_incoming_pckt <= '0';
         elsif dec_sop = '1' then
            reg_incoming_pckt <= '1';
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   --                          Check Part
   -- -------------------------------------------------------------------------

   -- Check instantion
   CHECKi: entity work.check
      generic map(
         MAC_COUNT      	=> MACS,
      	INBANDFCS         => INBANDFCS
      )
      port map(
         CLK            	=> CLK_INT,
         RESET          	=> RESET,

         DATA_RX        	=> dec_data,
         SOP_RX         	=> dec_sop,
         EOP_RX         	=> dec_eop,
         EOP_POS_RX     	=> dec_eop_pos,
         ERR_RX         	=> dec_err,

         DATA_TX        	=> check_data,
         SOP_TX         	=> check_sop,
         EOP_TX         	=> check_eop,
         EOP_POS_TX     	=> check_eop_pos,
         ERR_TX         	=> check_err,

         STATS          	=> check_stats,

         CAM_DI            => cam_data,
         CAM_MATCH_EN      => cam_match_en,
         CAM_MATCH_RST     => cam_match_rst,
         CAM_MATCH_BUS     => cam_match_bus,
         CAM_MATCH_BUS_VLD => cam_match_bus_vld,

         MI2CHECK       	=> mi2check,

         SAU_REQ        	=> SAU_REQ,
         SAU_ACCEPT     	=> SAU_ACCEPT,
         SAU_DV         	=> SAU_DV
      );

   -- -------------------------------------------------------------------------
   --                           Buf Part
   -- -------------------------------------------------------------------------

   -- Buf instantion
   BUFi: entity work.xgmii_ibuf_buf
      generic map(
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE,
         FL_WIDTH_TX    => FL_WIDTH_TX
      )
      port map(
         CLK            => CLK_INT,
         RESET          => RESET,

         RX_DATA        => check_data,
         RX_SOP         => check_sop,
         RX_EOP         => check_eop,
         RX_EOP_POS     => check_eop_pos,
         RX_ERR         => check_err,

         STATS          => check_stats,
         STATS_OUT      => STAT,
         STATS_OUT_VLD  => STAT_VLD,
         FRAME_RECEIVED => frame_receivedi,
         FRAME_DISCARDED=> frame_discardedi,
         BUFFER_OVF     => buffer_ovfi,

         FL_CLK         => FL_CLK,

         TX_DATA        => buf_data,
         TX_REM         => buf_rem,
         TX_SOP_N       => buf_sop_n,
         TX_EOP_N       => buf_eop_n,
         TX_SRC_RDY_N   => buf_src_rdy_n,
         TX_DST_RDY_N   => buf_dst_rdy_n,

         TX_HDATA       => buf_hdata,
         TX_HREM        => buf_hrem,
         TX_HSOP_N      => buf_hsop_n,
         TX_HEOP_N      => buf_heop_n,
         TX_HSRC_RDY_N  => buf_hsrc_rdy_n,
         TX_HDST_RDY_N  => buf_hdst_rdy_n,

         MI2BUF         => mi2buf,
         BUF2MI         => buf2mi,

         CTRL_DATA      => CTRL_DATA,
         CTRL_REM       => CTRL_REM,
         CTRL_SRC_RDY_N => CTRL_SRC_RDY_N,
         CTRL_SOP_N     => CTRL_SOP_N,
         CTRL_EOP_N     => CTRL_EOP_N,
         CTRL_DST_RDY_N => CTRL_DST_RDY_N,
         CTRL_REQ       => CTRL_REQ,
         CTRL_SEND      => CTRL_SEND,
         CTRL_RELEASE   => CTRL_RELEASE,
         CTRL_RDY       => CTRL_RDY
      );

   FRAME_RECEIVED  <= frame_receivedi;
   FRAME_DISCARDED <= frame_discardedi;
   BUFFER_OVF      <= buffer_ovfi;

   -- -------------------------------------------------------------------------
   --                        FL Composer Part
   -- -------------------------------------------------------------------------

   -- FL Composer instantion
   FL_COMPOSERi: entity work.fl_composer
      generic map(
         CTRL_HDR_EN    => CTRL_HDR_EN,
         CTRL_FTR_EN    => CTRL_FTR_EN,
         FL_WIDTH_TX    => FL_WIDTH_TX,
         FL_RELAY       => FL_RELAY
      )
      port map(
         CLK            => FL_CLK,
         RESET          => RESET,

         DEBUG_FIFO_SEL => composer_fifo_sel,

         RX_DATA        => buf_data,
         RX_REM         => buf_rem,
         RX_SOP_N       => buf_sop_n,
         RX_EOP_N       => buf_eop_n,
         RX_SRC_RDY_N   => buf_src_rdy_n,
         RX_DST_RDY_N   => buf_dst_rdy_n,

         RX_HDATA       => buf_hdata,
         RX_HREM        => buf_hrem,
         RX_HSOP_N      => buf_hsop_n,
         RX_HEOP_N      => buf_heop_n,
         RX_HSRC_RDY_N  => buf_hsrc_rdy_n,
         RX_HDST_RDY_N  => buf_hdst_rdy_n,

         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         TX_SOF_N       => TX_SOF_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_EOF_N       => TX_EOF_N,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N
      );


   -- -------------------------------------------------------------------------
   --                          MI Int Part
   -- -------------------------------------------------------------------------

   -- MI_INT instantion
   MI_INTi: entity work.mi_int
      generic map(
         MAC_COUNT         => MACS
      )
      port map(
         IBUF_CLK          => CLK_INT,
         RESET             => RESET,

         MI_CLK            => MI_CLK,
         MI_DWR      	   => MI_DWR,
      	MI_ADDR     	   => MI_ADDR,
      	MI_RD       	   => MI_RD,
      	MI_WR       	   => MI_WR,
      	MI_BE       	   => MI_BE,
      	MI_DRD      	   => MI_DRD,
      	MI_ARDY     	   => MI_ARDY,
      	MI_DRDY     	   => MI_DRDY,

         MI2CHECK          => mi2check,
         MI2BUF            => mi2buf,
         BUF2MI            => buf2mi,
         DEBUG_INFO(0)     => composer_fifo_sel,

         CAM_DI            => cam_data,
         CAM_MATCH_EN      => cam_match_en,
         CAM_MATCH_RST     => cam_match_rst,
         CAM_MATCH_BUS     => cam_match_bus,
         CAM_MATCH_BUS_VLD => cam_match_bus_vld
      );

end architecture ibuf_xgmii_sdr_norec_arch;
