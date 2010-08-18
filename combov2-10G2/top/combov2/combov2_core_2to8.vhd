-- combov2_core.vhd : Combov2 NetCOPE core
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.fl_pkg.all;
use work.addr_space.all;

architecture full of COMBOV2_CORE is

-- ----------------------------------------------------------------------------
--                          Components declaration
-- ----------------------------------------------------------------------------
component NETWORK_MOD_10G2_RX is
   port(
      -- Clock signal for user interface
      USER_CLK             :  in std_logic;
      -- FrameLink reset
      FL_RESET             :  in std_logic;
      -- ICS reset
      BUSRESET             :  in std_logic;

      -- 2 XGMII INTERFACES
      -- RX
      XGMII_RESET          :  in std_logic_vector(  1 downto 0);
      XGMII_RXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_RXD            :  in std_logic_vector(127 downto 0);
      XGMII_RXC            :  in std_logic_vector( 15 downto 0);
      -- TX
      XGMII_TXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_TXD            : out std_logic_vector(127 downto 0);
      XGMII_TXC            : out std_logic_vector( 15 downto 0);

      -- USER INTERFACE
      -- Network interface 0
      IBUF0_TX_SOF_N       : out std_logic;
      IBUF0_TX_SOP_N       : out std_logic;
      IBUF0_TX_EOP_N       : out std_logic;
      IBUF0_TX_EOF_N       : out std_logic;
      IBUF0_TX_SRC_RDY_N   : out std_logic;
      IBUF0_TX_DST_RDY_N   :  in std_logic;
      IBUF0_TX_DATA        : out std_logic_vector(127 downto 0);
      IBUF0_TX_REM         : out std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF0_CTRL_CLK       : out std_logic;
      IBUF0_CTRL_DATA      :  in std_logic_vector(127 downto 0);
      IBUF0_CTRL_REM       :  in std_logic_vector(3 downto 0);
      IBUF0_CTRL_SRC_RDY_N :  in std_logic;
      IBUF0_CTRL_SOP_N     :  in std_logic;
      IBUF0_CTRL_EOP_N     :  in std_logic;
      IBUF0_CTRL_DST_RDY_N : out std_logic;
      IBUF0_CTRL_RDY       :  in std_logic;

      -- IBUF status interface
      IBUF0_SOP            : out std_logic;
      IBUF0_PAYLOAD_LEN    : out std_logic_vector(15 downto 0);
      IBUF0_FRAME_ERROR    : out std_logic; -- 0: OK, 1: Error occured
      IBUF0_CRC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad CRC 
      IBUF0_MAC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad MAC
      IBUF0_LEN_BELOW_MIN  : out std_logic; -- 0: OK, 1: Length is below min
      IBUF0_LEN_OVER_MTU   : out std_logic; -- 0: OK, 1: Length is over MTU
      IBUF0_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT     :  in std_logic;
      IBUF0_SAU_DV         :  in std_logic;
      
      -- Network interface 1 --------------------------------------------------
      IBUF1_TX_SOF_N       : out std_logic;
      IBUF1_TX_SOP_N       : out std_logic;
      IBUF1_TX_EOP_N       : out std_logic;
      IBUF1_TX_EOF_N       : out std_logic;
      IBUF1_TX_SRC_RDY_N   : out std_logic;
      IBUF1_TX_DST_RDY_N   :  in std_logic;
      IBUF1_TX_DATA        : out std_logic_vector(127 downto 0);
      IBUF1_TX_REM         : out std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF1_CTRL_CLK       : out std_logic;
      IBUF1_CTRL_DATA      :  in std_logic_vector(127 downto 0);
      IBUF1_CTRL_REM       :  in std_logic_vector(3 downto 0);
      IBUF1_CTRL_SRC_RDY_N :  in std_logic;
      IBUF1_CTRL_SOP_N     :  in std_logic;
      IBUF1_CTRL_EOP_N     :  in std_logic;
      IBUF1_CTRL_DST_RDY_N : out std_logic;
      IBUF1_CTRL_RDY       :  in std_logic;

      -- IBUF status interface
      IBUF1_SOP            : out std_logic;
      IBUF1_PAYLOAD_LEN    : out std_logic_vector(15 downto 0);
      IBUF1_FRAME_ERROR    : out std_logic; -- 0: OK, 1: Error occured
      IBUF1_CRC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad CRC 
      IBUF1_MAC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad MAC
      IBUF1_LEN_BELOW_MIN  : out std_logic; -- 0: OK, 1: Length is below min
      IBUF1_LEN_OVER_MTU   : out std_logic; -- 0: OK, 1: Length is over MTU
      IBUF1_STAT_DV        : out std_logic;

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT     :  in std_logic;
      IBUF1_SAU_DV         :  in std_logic;

      -- Led interface
      IBUF_LED             : out std_logic_vector(1 downto 0);
      OBUF_LED             : out std_logic_vector(1 downto 0);
      
      -- Link presence interface 
      LINK0		   : out std_logic;
      LINK1		   : out std_logic;
 
      -- MI32 interface
      MI32_DWR             : in  std_logic_vector(31 downto 0);
      MI32_ADDR            : in  std_logic_vector(31 downto 0);
      MI32_RD              : in  std_logic;
      MI32_WR              : in  std_logic;
      MI32_BE              : in  std_logic_vector(3 downto 0);
      MI32_DRD             : out std_logic_vector(31 downto 0);
      MI32_ARDY            : out std_logic;
      MI32_DRDY            : out std_logic
   );
end component;

component DMA_MOD_Nx64b_RX is
   generic (
      IFCS           : integer
   );
   port(
      -- ICS Clock (IB and LB)
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- User Clock (FrameLink)
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      RX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input interface
      RX_DATA       : in  std_logic_vector(IFCS*64-1 downto 0);
      RX_DREM       : in  std_logic_vector(IFCS*3-1 downto 0);
      RX_SOF_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_EOF_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_SOP_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_EOP_N      : in  std_logic_vector(IFCS-1 downto 0);
      RX_SRC_RDY_N  : in  std_logic_vector(IFCS-1 downto 0);
      RX_DST_RDY_N  : out std_logic_vector(IFCS-1 downto 0);

      -- Internal Bus
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end component;

-- input buffer for differencial pair
component IBUFDS
port (
   O  : out std_logic;
   I  : in  std_logic;
   IB : in  std_logic
);
end component;

-- output buffer for differencial pair
component OBUFDS
port (
   OB : out std_logic;
   O  : out std_logic;
   I  : in  std_logic
);
end component;

-- output buffer
component OBUF
port (
   O  : out std_logic;
   I  : in  std_logic
);
end component;

-- Chipscope ICON
component icon3 is
   port (
      CONTROL0 : inout std_logic_vector(35 downto 0);
      CONTROL1 : inout std_logic_vector(35 downto 0);
      CONTROL2 : inout std_logic_vector(35 downto 0)
   );
end component;

-- Chipscope ILA (144-bit trigger port)
component ila144 is
   port (
      CONTROL : inout std_logic_vector(35 downto 0);
      CLK     : in std_logic;
      TRIG0   : in std_logic_vector(143 downto 0)
   );
end component;

-- Chipscope ILA (72-bit trigger port)
component ila72 is
   port (
      CONTROL : inout std_logic_vector(35 downto 0);
      CLK     : in std_logic;
      TRIG0   : in std_logic_vector(71 downto 0)
   );
end component;

-- ----------------------------------------------------------------------------
--                            Signal declaration
-- ----------------------------------------------------------------------------

   constant DMA_FLOWS         : integer := 8;
   -- ------------------------------------------------------------------------
   --                          DMA module signals
   -- ------------------------------------------------------------------------
   -- DMA module buffers FrameLink
   signal swbuf_data       : std_logic_vector(DMA_FLOWS*64-1 downto 0);
   signal swbuf_drem       : std_logic_vector(DMA_FLOWS*3-1 downto 0);
   signal swbuf_sof_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal swbuf_eof_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal swbuf_sop_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal swbuf_eop_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal swbuf_src_rdy_n  : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal swbuf_dst_rdy_n  : std_logic_vector(DMA_FLOWS-1 downto 0);


   -- Interrupts signals
   signal rx_interrupt        : std_logic;

   -- ------------------------------------------------------------------------
   --                        Network module signals
   -- ------------------------------------------------------------------------
   signal ibuf0_pacodag_clk       : std_logic;
   signal ibuf0_pacodag_data      : std_logic_vector(127 downto 0);
   signal ibuf0_pacodag_rem       : std_logic_vector(  3 downto 0);
   signal ibuf0_pacodag_src_rdy_n : std_logic;
   signal ibuf0_pacodag_sop_n     : std_logic;
   signal ibuf0_pacodag_eop_n     : std_logic;
   signal ibuf0_pacodag_dst_rdy_n : std_logic;
   signal ibuf0_pacodag_rdy       : std_logic; -- PCD is ready for next request
   signal ibuf0_pacodag_sop       : std_logic;
   signal ibuf0_pacodag_stat      : t_ibuf_general_stat;
   signal ibuf0_pacodag_stat_dv   : std_logic;
   signal ibuf0_sau_accept    : std_logic;
   signal ibuf0_sau_dv        : std_logic;

   signal ibuf1_pacodag_clk       : std_logic;
   signal ibuf1_pacodag_data      : std_logic_vector(127 downto 0);
   signal ibuf1_pacodag_rem       : std_logic_vector(  3 downto 0);
   signal ibuf1_pacodag_src_rdy_n : std_logic;
   signal ibuf1_pacodag_sop_n     : std_logic;
   signal ibuf1_pacodag_eop_n     : std_logic;
   signal ibuf1_pacodag_dst_rdy_n : std_logic;
   signal ibuf1_pacodag_rdy       : std_logic; -- PCD is ready for next request
   signal ibuf1_pacodag_sop       : std_logic;
   signal ibuf1_pacodag_stat      : t_ibuf_general_stat;
   signal ibuf1_pacodag_stat_dv   : std_logic;
   signal ibuf1_sau_accept    : std_logic;
   signal ibuf1_sau_dv        : std_logic;

   attribute buffer_type:string;
   attribute buffer_type of ibuf1_pacodag_clk:signal is "none";
   attribute buffer_type of ibuf0_pacodag_clk:signal is "none";

   -- IBUFs to output FrameLink
   signal ibuf0_tx     : t_fl128;
   signal ibuf1_tx     : t_fl128;

   -- ------------------------------------------------------------------------
   --                            Other signals
   -- ------------------------------------------------------------------------

   -- Internal bus signals ---------------------
   signal ibus_down_data         : std_logic_vector(63 downto 0);
   signal ibus_down_sof_n        : std_logic;
   signal ibus_down_eof_n        : std_logic;
   signal ibus_down_src_rdy_n    : std_logic;
   signal ibus_down_dst_rdy_n    : std_logic;
   signal ibus_up_data           : std_logic_vector(63 downto 0);
   signal ibus_up_sof_n          : std_logic;
   signal ibus_up_eof_n          : std_logic;
   signal ibus_up_src_rdy_n      : std_logic;
   signal ibus_up_dst_rdy_n      : std_logic;

   -- Chipscope signals
   signal control0            : std_logic_vector(35 downto 0);
   signal control1            : std_logic_vector(35 downto 0);
   signal control2            : std_logic_vector(35 downto 0);
   signal ila144_ib_trig      : std_logic_vector(143 downto 0);
   signal ila144_fl_trig      : std_logic_vector(143 downto 0);
   signal ila144_mi_trig      : std_logic_vector(143 downto 0);

   -- attributes to prevent optimization in precision
   attribute dont_touch : string;
   attribute dont_touch of MCLK0_IBUFDS : label is "true";
   attribute dont_touch of MCLK1_IBUFDS : label is "true";
   attribute dont_touch of XCLK0_IBUFDS : label is "true";
   attribute dont_touch of XCLK1_IBUFDS : label is "true";
   attribute dont_touch of XCLK2_IBUFDS : label is "true";
   attribute dont_touch of GCLK100_IBUFDS : label is "true";
   attribute dont_touch of GCLK250_IBUFDS : label is "true";

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                        USER APPLICATION MODULE
   -- -------------------------------------------------------------------------
   APPLICATION_I : entity work.APPLICATION_SPLITTER_2x128toNx64
   generic map (
      DMA_FLOWS      => DMA_FLOWS
   )
   port map (
      CLK                  => CLK_USER0,
      RESET                => RESET_USER0,

      -- ----------------------------------------------------------------------
      -- NETWORK INTERFACE 0
      -- ----------------------------------------------------------------------
      -- Input buffer interface
      IBUF0_TX_SOF_N       => ibuf0_tx.sof_n,
      IBUF0_TX_SOP_N       => ibuf0_tx.sop_n,
      IBUF0_TX_EOP_N       => ibuf0_tx.eop_n,
      IBUF0_TX_EOF_N       => ibuf0_tx.eof_n,
      IBUF0_TX_SRC_RDY_N   => ibuf0_tx.src_rdy_n,
      IBUF0_TX_DST_RDY_N   => ibuf0_tx.dst_rdy_n,
      IBUF0_TX_DATA        => ibuf0_tx.data,
      IBUF0_TX_REM         => ibuf0_tx.drem,
                                                   
      -- PACODAG interface                         
      IBUF0_CTRL_CLK       => ibuf0_pacodag_clk,
      IBUF0_CTRL_DATA      => ibuf0_pacodag_data,
      IBUF0_CTRL_REM       => ibuf0_pacodag_rem,
      IBUF0_CTRL_SRC_RDY_N => ibuf0_pacodag_src_rdy_n,
      IBUF0_CTRL_SOP_N     => ibuf0_pacodag_sop_n,
      IBUF0_CTRL_EOP_N     => ibuf0_pacodag_eop_n,
      IBUF0_CTRL_DST_RDY_N => ibuf0_pacodag_dst_rdy_n,
      IBUF0_CTRL_RDY       => ibuf0_pacodag_rdy,
                                                   
      -- IBUF status interface
      IBUF0_SOP            => ibuf0_pacodag_sop,
      IBUF0_PAYLOAD_LEN    => ibuf0_pacodag_stat.payload_len,
      IBUF0_FRAME_ERROR    => ibuf0_pacodag_stat.frame_error,
      IBUF0_CRC_CHECK_FAILED=>ibuf0_pacodag_stat.crc_check_failed,
      IBUF0_MAC_CHECK_FAILED=>ibuf0_pacodag_stat.mac_check_failed,
      IBUF0_LEN_BELOW_MIN  => ibuf0_pacodag_stat.len_below_min,
      IBUF0_LEN_OVER_MTU   => ibuf0_pacodag_stat.len_over_mtu,
      IBUF0_STAT_DV        => ibuf0_pacodag_stat_dv,

      -- ----------------------------------------------------------------------
      -- NETWORK INTERFACE 1
      -- ----------------------------------------------------------------------
      -- Input buffer interface                        
      IBUF1_TX_SOF_N       => ibuf1_tx.sof_n,
      IBUF1_TX_SOP_N       => ibuf1_tx.sop_n,
      IBUF1_TX_EOP_N       => ibuf1_tx.eop_n,
      IBUF1_TX_EOF_N       => ibuf1_tx.eof_n,
      IBUF1_TX_SRC_RDY_N   => ibuf1_tx.src_rdy_n,
      IBUF1_TX_DST_RDY_N   => ibuf1_tx.dst_rdy_n,
      IBUF1_TX_DATA        => ibuf1_tx.data,
      IBUF1_TX_REM         => ibuf1_tx.drem,

      -- PACODAG interface                         
      IBUF1_CTRL_CLK       => ibuf1_pacodag_clk, 
      IBUF1_CTRL_DATA      => ibuf1_pacodag_data,
      IBUF1_CTRL_REM       => ibuf1_pacodag_rem,
      IBUF1_CTRL_SRC_RDY_N => ibuf1_pacodag_src_rdy_n,
      IBUF1_CTRL_SOP_N     => ibuf1_pacodag_sop_n,
      IBUF1_CTRL_EOP_N     => ibuf1_pacodag_eop_n,
      IBUF1_CTRL_DST_RDY_N => ibuf1_pacodag_dst_rdy_n,
      IBUF1_CTRL_RDY       => ibuf1_pacodag_rdy,

      -- IBUF status interface
      IBUF1_SOP            => ibuf1_pacodag_sop,
      IBUF1_PAYLOAD_LEN    => ibuf1_pacodag_stat.payload_len,
      IBUF1_FRAME_ERROR    => ibuf1_pacodag_stat.frame_error,
      IBUF1_CRC_CHECK_FAILED=>ibuf1_pacodag_stat.crc_check_failed,
      IBUF1_MAC_CHECK_FAILED=>ibuf1_pacodag_stat.mac_check_failed,
      IBUF1_LEN_BELOW_MIN  => ibuf1_pacodag_stat.len_below_min,
      IBUF1_LEN_OVER_MTU   => ibuf1_pacodag_stat.len_over_mtu,
      IBUF1_STAT_DV        => ibuf1_pacodag_stat_dv,

      -- ----------------------------------------------------------------------
      -- DMA INTERFACE
      -- ----------------------------------------------------------------------
      TX_DATA       => swbuf_data,
      TX_DREM       => swbuf_drem,
      TX_SOF_N      => swbuf_sof_n,
      TX_EOF_N      => swbuf_eof_n,
      TX_SOP_N      => swbuf_sop_n,
      TX_EOP_N      => swbuf_eop_n,
      TX_SRC_RDY_N  => swbuf_src_rdy_n,
      TX_DST_RDY_N  => swbuf_dst_rdy_n,

      -- ----------------------------------------------------------------------
      -- ICS INTERFACE
      -- ----------------------------------------------------------------------
      -- MI32 interface
      MI32_DWR          => MI32_USER_DWR,
      MI32_ADDR         => MI32_USER_ADDR,
      MI32_RD           => MI32_USER_RD,
      MI32_WR           => MI32_USER_WR,
      MI32_BE           => MI32_USER_BE,
      MI32_DRD          => MI32_USER_DRD_aux,
      MI32_ARDY         => MI32_USER_ARDY_aux,
      MI32_DRDY         => MI32_USER_DRDY_aux,

      -- ----------------------------------------------------------------------
      -- PPS signal from PTM card with GPS
      -- ----------------------------------------------------------------------
      PPS_N          => PPS_N;

      -- ----------------------------------------------------------------------
      -- CLK signal from PTM card precise crystal
      -- ----------------------------------------------------------------------
      PTM_CLK        => PTM_CLK
   );
   
   MI32_USER_DRD  <= MI32_USER_DRD_aux;
   MI32_USER_ARDY <= MI32_USER_ARDY_aux;
   MI32_USER_DRDY <= MI32_USER_DRDY_aux;
   
   -- -------------------------------------------------------------------------
   --                            EMPTY SAU
   -- -------------------------------------------------------------------------
   ibuf0_sau_accept <= '1';
   ibuf0_sau_dv     <= '1';
   ibuf1_sau_accept <= '1';
   ibuf1_sau_dv     <= '1';

   -- -------------------------------------------------------------------------
   --                            NETWORK MODULE
   -- -------------------------------------------------------------------------
   NETWORK_MODULE_I : NETWORK_MOD_10G2_RX
   port map(
      USER_CLK          => CLK_USER0,
      FL_RESET          => RESET_USER0,
      BUSRESET          => RESET_USER0,

      -- 2 XGMII interfaces
      -- RX
      XGMII_RESET    => XGMII_RESET,
      XGMII_RXCLK    => XGMII_RXCLK,
      XGMII_RXD      => XGMII_RXD,
      XGMII_RXC      => XGMII_RXC,

      -- TX
      XGMII_TXCLK    => XGMII_TXCLK,
      XGMII_TXD      => XGMII_TXD,
      XGMII_TXC      => XGMII_TXC,

      -- USER INTERFACE
      -- Network interface 0
      IBUF0_TX_SOF_N       => ibuf0_tx.sof_n,
      IBUF0_TX_SOP_N       => ibuf0_tx.sop_n,
      IBUF0_TX_EOP_N       => ibuf0_tx.eop_n,
      IBUF0_TX_EOF_N       => ibuf0_tx.eof_n,
      IBUF0_TX_SRC_RDY_N   => ibuf0_tx.src_rdy_n,
      IBUF0_TX_DST_RDY_N   => ibuf0_tx.dst_rdy_n,
      IBUF0_TX_DATA        => ibuf0_tx.data,
      IBUF0_TX_REM         => ibuf0_tx.drem,

      -- PACODAG interface
      IBUF0_CTRL_CLK       => ibuf0_pacodag_clk,
      IBUF0_CTRL_DATA      => ibuf0_pacodag_data,
      IBUF0_CTRL_REM       => ibuf0_pacodag_rem,
      IBUF0_CTRL_SRC_RDY_N => ibuf0_pacodag_src_rdy_n,
      IBUF0_CTRL_SOP_N     => ibuf0_pacodag_sop_n,
      IBUF0_CTRL_EOP_N     => ibuf0_pacodag_eop_n,
      IBUF0_CTRL_DST_RDY_N => ibuf0_pacodag_dst_rdy_n,
      IBUF0_CTRL_RDY       => ibuf0_pacodag_rdy,

      -- IBUF status interface
      IBUF0_SOP            => ibuf0_pacodag_sop,
      IBUF0_PAYLOAD_LEN    => ibuf0_pacodag_stat.payload_len,
      IBUF0_FRAME_ERROR    => ibuf0_pacodag_stat.frame_error,
      IBUF0_CRC_CHECK_FAILED=>ibuf0_pacodag_stat.crc_check_failed,
      IBUF0_MAC_CHECK_FAILED=>ibuf0_pacodag_stat.mac_check_failed,
      IBUF0_LEN_BELOW_MIN  => ibuf0_pacodag_stat.len_below_min,
      IBUF0_LEN_OVER_MTU   => ibuf0_pacodag_stat.len_over_mtu,
      IBUF0_STAT_DV        => ibuf0_pacodag_stat_dv,

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT     => ibuf0_sau_accept,
      IBUF0_SAU_DV         => ibuf0_sau_dv,
      
      -- Network interface 1 --------------------------------------------------
      IBUF1_TX_SOF_N       => ibuf1_tx.sof_n,
      IBUF1_TX_SOP_N       => ibuf1_tx.sop_n,
      IBUF1_TX_EOP_N       => ibuf1_tx.eop_n,
      IBUF1_TX_EOF_N       => ibuf1_tx.eof_n,
      IBUF1_TX_SRC_RDY_N   => ibuf1_tx.src_rdy_n,
      IBUF1_TX_DST_RDY_N   => ibuf1_tx.dst_rdy_n,
      IBUF1_TX_DATA        => ibuf1_tx.data,
      IBUF1_TX_REM         => ibuf1_tx.drem,

      -- PACODAG interface
      IBUF1_CTRL_CLK       => ibuf1_pacodag_clk,
      IBUF1_CTRL_DATA      => ibuf1_pacodag_data,
      IBUF1_CTRL_REM       => ibuf1_pacodag_rem,
      IBUF1_CTRL_SRC_RDY_N => ibuf1_pacodag_src_rdy_n,
      IBUF1_CTRL_SOP_N     => ibuf1_pacodag_sop_n,
      IBUF1_CTRL_EOP_N     => ibuf1_pacodag_eop_n,
      IBUF1_CTRL_DST_RDY_N => ibuf1_pacodag_dst_rdy_n,
      IBUF1_CTRL_RDY       => ibuf1_pacodag_rdy,

      -- IBUF status interface
      IBUF1_SOP            => ibuf1_pacodag_sop,
      IBUF1_PAYLOAD_LEN    => ibuf1_pacodag_stat.payload_len,
      IBUF1_FRAME_ERROR    => ibuf1_pacodag_stat.frame_error,
      IBUF1_CRC_CHECK_FAILED=>ibuf1_pacodag_stat.crc_check_failed,
      IBUF1_MAC_CHECK_FAILED=>ibuf1_pacodag_stat.mac_check_failed,
      IBUF1_LEN_BELOW_MIN  => ibuf1_pacodag_stat.len_below_min,
      IBUF1_LEN_OVER_MTU   => ibuf1_pacodag_stat.len_over_mtu,
      IBUF1_STAT_DV        => ibuf1_pacodag_stat_dv,

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT     => ibuf1_sau_accept,
      IBUF1_SAU_DV         => ibuf1_sau_dv,

      -- Led interface
      IBUF_LED             => IBUF_LED,
      OBUF_LED             => OBUF_LED,

      -- Link presence interface
      LINK0		   => open,
      LINK1		   => open,

      -- MI32 interface
      MI32_DWR             => MI32_NET_DWR,
      MI32_ADDR            => MI32_NET_ADDR,
      MI32_RD              => MI32_NET_RD,
      MI32_WR              => MI32_NET_WR,
      MI32_BE              => MI32_NET_BE,
      MI32_DRD             => MI32_NET_DRD_aux,
      MI32_ARDY            => MI32_NET_ARDY_aux,
      MI32_DRDY            => MI32_NET_DRDY_aux
   );
   
   MI32_NET_DRD  <= MI32_NET_DRD_aux;
   MI32_NET_ARDY <= MI32_NET_ARDY_aux;
   MI32_NET_DRDY <= MI32_NET_DRDY_aux;
   
   -- -------------------------------------------------------------------------
   --                              DMA engine
   -- -------------------------------------------------------------------------
   DMA_MOD_I : DMA_MOD_Nx64b_RX
   generic map (
      IFCS           => DMA_FLOWS
   )
   port map(
      -- Common interface
      CLK            => CLK_ICS,
      RESET          => RESET_ICS,

      USER_CLK       => CLK_USER0,
      USER_RESET     => RESET_USER0,

      RX_INTERRUPT   => rx_interrupt,
      -- network interfaces - USER_CLK
      -- input interface
      RX_DATA        => swbuf_data,
      RX_DREM        => swbuf_drem,
      RX_SOF_N       => swbuf_sof_n,
      RX_EOF_N       => swbuf_eof_n,
      RX_SOP_N       => swbuf_sop_n,
      RX_EOP_N       => swbuf_eop_n,
      RX_SRC_RDY_N   => swbuf_src_rdy_n,
      RX_DST_RDY_N   => swbuf_dst_rdy_n,

      -- Internal Bus
      IB_DOWN_DATA      => ibus_down_data,
      IB_DOWN_SOF_N     => ibus_down_sof_n,
      IB_DOWN_EOF_N     => ibus_down_eof_n,
      IB_DOWN_SRC_RDY_N => ibus_down_src_rdy_n,
      IB_DOWN_DST_RDY_N => ibus_down_dst_rdy_n,
      IB_UP_DATA        => ibus_up_data,
      IB_UP_SOF_N       => ibus_up_sof_n,
      IB_UP_EOF_N       => ibus_up_eof_n,
      IB_UP_SRC_RDY_N   => ibus_up_src_rdy_n,
      IB_UP_DST_RDY_N   => ibus_up_dst_rdy_n,

      -- MI32 interface
      MI32_DWR          => MI32_DMA_DWR,
      MI32_ADDR         => MI32_DMA_ADDR,
      MI32_RD           => MI32_DMA_RD,
      MI32_WR           => MI32_DMA_WR,
      MI32_BE           => MI32_DMA_BE,
      MI32_DRD          => MI32_DMA_DRD_aux,
      MI32_ARDY         => MI32_DMA_ARDY_aux,
      MI32_DRDY         => MI32_DMA_DRDY_aux
   );

   -- Interface mapping
   ibus_down_data      <= IB_DOWN_DATA;
   ibus_down_sof_n     <= IB_DOWN_SOF_N;
   ibus_down_eof_n     <= IB_DOWN_EOF_N;
   ibus_down_src_rdy_n <= IB_DOWN_SRC_RDY_N;
   IB_DOWN_DST_RDY_N   <= ibus_down_dst_rdy_n;

   IB_UP_DATA        <= ibus_up_data;
   IB_UP_SOF_N       <= ibus_up_sof_n;
   IB_UP_EOF_N       <= ibus_up_eof_n;
   IB_UP_SRC_RDY_N   <= ibus_up_src_rdy_n;
   ibus_up_dst_rdy_n <= IB_UP_DST_RDY_N;
   
   MI32_DMA_DRD  <= MI32_DMA_DRD_aux;
   MI32_DMA_ARDY <= MI32_DMA_ARDY_aux;
   MI32_DMA_DRDY <= MI32_DMA_DRDY_aux;
   
   INTERRUPT <= rx_interrupt;
   INTR_DATA <= "00000";
   -- INTR_RDY open -- TODO: deal with INTR_RDY=0, because otherwise
   -- an interrupt may be lost

   -- -------------------------------------------------------------------------
   --                             CHIPSCOPE
   -- -------------------------------------------------------------------------

--    GEN_CHIPSCOPE : if (GENERATE_CHIPSCOPE = true) generate
   CSCOPE: if (true) generate

      -- Attributes (Precision)
      attribute dont_touch of ICON3_I     : label is "true";
      attribute dont_touch of ILA144_IB_I : label is "true";
      attribute dont_touch of ILA144_FL_I : label is "true";
      attribute dont_touch of ILA144_MI_I : label is "true";

   begin

      -- Chipscope ICON with 3 ports
      ICON3_I : icon3
      port map(
        CONTROL0 => control0,
        CONTROL1 => control1,
        CONTROL2 => control2
      );

      -- Chipscope ILA with 144-bit trigger port - INTERNAL BUS
      ila144_ib_trig <= "00000000"            -- unused (8 bits)
                      & ibus_up_data         -- upstream port
                      & ibus_up_sof_n
                      & ibus_up_eof_n
                      & ibus_up_src_rdy_n
                      & ibus_up_dst_rdy_n
                      & ibus_down_data       -- downstream port
                      & ibus_down_sof_n
                      & ibus_down_eof_n
                      & ibus_down_src_rdy_n
                      & ibus_down_dst_rdy_n;

      ILA144_IB_I : ila144
      port map(
         CONTROL => control0,
         CLK     => CLK_ICS,
         TRIG0   => ila144_ib_trig
      );

      -- Chipscope ILA with 144-bit trigger port - FRAMELINK interface 0
      ila144_fl_trig <= ibuf0_tx.DATA      -- TX0 port
                      & ibuf0_tx.DREM
                      & ibuf0_tx.SOF_N
                      & ibuf0_tx.SOP_N
                      & ibuf0_tx.EOP_N
                      & ibuf0_tx.EOF_N
                      & ibuf0_tx.SRC_RDY_N
                      & ibuf0_tx.DST_RDY_N
                      & ibuf1_tx.DATA      -- TX1 port
                      & ibuf1_tx.DREM
                      & ibuf1_tx.SOF_N
                      -- & ibuf1_tx.SOP_N
                      -- & ibuf1_tx.EOP_N
                      & ibuf1_tx.EOF_N
                      & ibuf1_tx.SRC_RDY_N
                      & ibuf1_tx.DST_RDY_N;

      ILA144_FL_I : ila144
      port map(
         CONTROL => control1,
         CLK     => CLK_USER0,
         TRIG0   => ila144_fl_trig
      );

      -- Chipscope ILA with 144-bit trigger port - DMA MI32 interface
      ila144_mi_trig <= "0000000000000000000000000000000000000000" -- unused (40 bits)  
                     -- MI to DMA module
                     & MI32_DMA_DWR
                     & MI32_DMA_ADDR
                     & MI32_DMA_RD
                     & MI32_DMA_WR
                     & MI32_DMA_ARDY_aux
                     & MI32_DMA_BE
                     & MI32_DMA_DRD_aux
                     & MI32_DMA_DRDY_aux;

-- Don't forget to change CLK to ila144 if you connect another MI interface!

--                      -- MI to Application (only control signals)
--                      & MI32_USER_DWR 
--                      & MI32_USER_ADDR
--                      & MI32_USER_RD
--                      & MI32_USER_WR
--                      & MI32_USER_ARDY_aux
--                      & MI32_USER_BE
--                      & MI32_USER_DRD_aux
--                      & MI32_USER_DRDY_aux;

--                      -- MI to Network mod (only control signals)
--                      & MI32_NET_DWR
--                      & MI32_NET_ADDR
--                      & MI32_NET_RD
--                      & MI32_NET_WR
--                      & MI32_NET_ARDY_aux
--                      & MI32_NET_BE
--                      & MI32_NET_DRD_aux
--                      & MI32_NET_DRDY_aux;

      ILA144_MI_I : ila144
      port map(
         CONTROL => control2,
         CLK     => CLK_ICS,
         TRIG0   => ila144_mi_trig
      );

   end generate;

-- ------------------------------------------------------------------------
-- These signals are unused in NIC, but may be used in other projects
-- ------------------------------------------------------------------------
   -- Clocks
   MCLK0_IBUFDS : IBUFDS
   port map(
      I  => MCLK0_P,
      IB => MCLK0_N,
      O  => open
   );
   MCLK1_IBUFDS : IBUFDS
   port map(
      I  => MCLK1_P,
      IB => MCLK1_N,
      O  => open
   );
   GCLK250_IBUFDS : IBUFDS
   port map(
      I  => GCLK250_P,
      IB => GCLK250_N,
      O  => open
   );
   GCLK100_IBUFDS : IBUFDS
   port map(
      I  => GCLK100_P,
      IB => GCLK100_N,
      O  => open
   );
   XCLK2_IBUFDS : IBUFDS
   port map(
      I  => XCLK2_P,
      IB => XCLK2_N,
      O  => open
   );
   XCLK1_IBUFDS : IBUFDS
   port map(
      I  => XCLK1_P,
      IB => XCLK1_N,
      O  => open
   );
   XCLK0_IBUFDS : IBUFDS
   port map(
      I  => XCLK0_P,
      IB => XCLK0_N,
      O  => open
   );

   -- SRAM (no errors reported)

   -- DRAM
   DSCL_OBUF : OBUF
   port map(
      O  => DSCL,
      I  => reset_ics
   );
   DWE_N_OBUF : OBUF
   port map(
      O  => DWE_N,
      I  => reset_ics
   );
   DCAS_N_OBUF : OBUF
   port map(
      O  => DCAS_N,
      I  => reset_ics
   );
   DRAS_N_OBUF : OBUF
   port map(
      O  => DRAS_N,
      I  => reset_ics
   );
   DCK0_P_OBUF : OBUF
   port map(
      O  => DCK0_P,
      I  => reset_ics
   );
   DCK0_N_OBUF : OBUF
   port map(
      O  => DCK0_N,
      I  => reset_ics
   );
   DCK1_P_OBUF : OBUF
   port map(
      O  => DCK1_P,
      I  => reset_ics
   );
   DCK1_N_OBUF : OBUF
   port map(
      O  => DCK1_N,
      I  => reset_ics
   );
   DA_OBUF_GEN: for i in 0 to 13 generate
      DA_OBUF : OBUF
      port map(
         O  => DA(i),
         I  => reset_ics
      );
   end generate;
   DBA_OBUF_GEN: for i in 0 to 2 generate
      DBA_OBUF : OBUF
      port map(
         O  => DBA(i),
         I  => reset_ics
      );
   end generate;
   DSA_OBUF_GEN: for i in 0 to 1 generate
      DSA_OBUF : OBUF
      port map(
         O  => DSA(i),
         I  => reset_ics
      );
   end generate;
   DDODT_OBUF_GEN: for i in 0 to 1 generate
      DDODT_OBUF : OBUF
      port map(
         O  => DDODT(i),
         I  => reset_ics
      );
   end generate;
   DCS_N_OBUF_GEN: for i in 0 to 1 generate
      DCS_N_OBUF : OBUF
      port map(
         O  => DCS_N(i),
         I  => reset_ics
      );
   end generate;
   DCKE_OBUF_GEN: for i in 0 to 1 generate
      DCKE_OBUF : OBUF
      port map(
         O  => DCKE(i),
         I  => reset_ics
      );
   end generate;

   -- Misc
   FQTXD_OBUF : OBUF
   port map(
      O  => FQTXD,
      I  => reset_ics
   );
   FQLED_OBUF_GEN: for i in 0 to 3 generate
      FQLED_OBUF : OBUF
      port map(
         O  => FQLED(i),
         I  => reset_ics
      );
   end generate;



end architecture full;

