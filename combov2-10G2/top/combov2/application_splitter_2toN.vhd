-- application_splitter_2toN.vhd : Combov2 NetCOPE application architecture
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.fl_pkg.all;
use work.addr_space.all;
use work.network_mod_10g2_const.all;

entity APPLICATION_SPLITTER_2x128toNx64 is
   generic (
      -- defines number of flows which are input streams splitted into
      DMA_FLOWS      : integer := 8
   );
   port (
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESETs
      -- ----------------------------------------------------------------------
      -- Clock signal for user interface
      CLK                  : in std_logic; --  set DIV constants to derive from 1GHz

      -- Global reset
      RESET                : in std_logic;

      -- ----------------------------------------------------------------------
      -- NETWORK INTERFACE 0
      -- ----------------------------------------------------------------------
      -- Input buffer interface
      IBUF0_TX_SOF_N       :  in std_logic;
      IBUF0_TX_SOP_N       :  in std_logic;
      IBUF0_TX_EOP_N       :  in std_logic;
      IBUF0_TX_EOF_N       :  in std_logic;
      IBUF0_TX_SRC_RDY_N   :  in std_logic;
      IBUF0_TX_DST_RDY_N   : out std_logic;
      IBUF0_TX_DATA        :  in std_logic_vector(127 downto 0);
      IBUF0_TX_REM         :  in std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF0_CTRL_CLK       :  in std_logic;
      IBUF0_CTRL_DATA      : out std_logic_vector(127 downto 0);
      IBUF0_CTRL_REM       : out std_logic_vector(3 downto 0);
      IBUF0_CTRL_SRC_RDY_N : out std_logic;
      IBUF0_CTRL_SOP_N     : out std_logic;
      IBUF0_CTRL_EOP_N     : out std_logic;
      IBUF0_CTRL_DST_RDY_N :  in std_logic;
      IBUF0_CTRL_RDY       : out std_logic;

      -- IBUF status interface
      IBUF0_SOP            :  in std_logic;
      IBUF0_PAYLOAD_LEN    :  in std_logic_vector(15 downto 0);
      IBUF0_FRAME_ERROR    :  in std_logic; -- 0: OK, 1: Error occured
      IBUF0_CRC_CHECK_FAILED: in std_logic; -- 0: OK, 1: Bad CRC 
      IBUF0_MAC_CHECK_FAILED: in std_logic; -- 0: OK, 1: Bad MAC
      IBUF0_LEN_BELOW_MIN  :  in std_logic; -- 0: OK, 1: Length is below min
      IBUF0_LEN_OVER_MTU   :  in std_logic; -- 0: OK, 1: Length is over MTU
      IBUF0_STAT_DV        :  in std_logic;

      -- ----------------------------------------------------------------------
      -- NETWORK INTERFACE 1
      -- ----------------------------------------------------------------------
      -- Input buffer interface
      IBUF1_TX_SOF_N       :  in std_logic;
      IBUF1_TX_SOP_N       :  in std_logic;
      IBUF1_TX_EOP_N       :  in std_logic;
      IBUF1_TX_EOF_N       :  in std_logic;
      IBUF1_TX_SRC_RDY_N   :  in std_logic;
      IBUF1_TX_DST_RDY_N   : out std_logic;
      IBUF1_TX_DATA        :  in std_logic_vector(127 downto 0);
      IBUF1_TX_REM         :  in std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF1_CTRL_CLK       :  in std_logic;
      IBUF1_CTRL_DATA      : out std_logic_vector(127 downto 0);
      IBUF1_CTRL_REM       : out std_logic_vector(3 downto 0);
      IBUF1_CTRL_SRC_RDY_N : out std_logic;
      IBUF1_CTRL_SOP_N     : out std_logic;
      IBUF1_CTRL_EOP_N     : out std_logic;
      IBUF1_CTRL_DST_RDY_N :  in std_logic;
      IBUF1_CTRL_RDY       : out std_logic;

      -- IBUF status interface
      IBUF1_SOP            :  in std_logic;
      IBUF1_PAYLOAD_LEN    :  in std_logic_vector(15 downto 0);
      IBUF1_FRAME_ERROR    :  in std_logic; -- 0: OK, 1: Error occured
      IBUF1_CRC_CHECK_FAILED: in std_logic; -- 0: OK, 1: Bad CRC 
      IBUF1_MAC_CHECK_FAILED: in std_logic; -- 0: OK, 1: Bad MAC
      IBUF1_LEN_BELOW_MIN  :  in std_logic; -- 0: OK, 1: Length is below min
      IBUF1_LEN_OVER_MTU   :  in std_logic; -- 0: OK, 1: Length is over MTU
      IBUF1_STAT_DV        :  in std_logic;

      -- ----------------------------------------------------------------------
      -- DMA INTERFACE
      -- ----------------------------------------------------------------------
      TX_DATA       : out std_logic_vector(DMA_FLOWS*64-1 downto 0);
      TX_DREM       : out std_logic_vector(DMA_FLOWS*3-1 downto 0);
      TX_SOF_N      : out std_logic_vector(DMA_FLOWS-1 downto 0);
      TX_EOF_N      : out std_logic_vector(DMA_FLOWS-1 downto 0);
      TX_SOP_N      : out std_logic_vector(DMA_FLOWS-1 downto 0);
      TX_EOP_N      : out std_logic_vector(DMA_FLOWS-1 downto 0);
      TX_SRC_RDY_N  : out std_logic_vector(DMA_FLOWS-1 downto 0);
      TX_DST_RDY_N  :  in std_logic_vector(DMA_FLOWS-1 downto 0);

      -- ----------------------------------------------------------------------
      -- ICS INTERFACE
      -- ----------------------------------------------------------------------
      -- Internal Bus interface (Fast)
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;

      -- MI32 interface (Slow, efficient)
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic;

      -- -------------------------------------------------------------------
      -- TIMESTAMPS FOR PACODAG
      -- -------------------------------------------------------------------
      TS             : in std_logic_vector(63 downto 0); 
      TS_DV          : in std_logic;
      TS_CLK         : in std_logic
   );

end APPLICATION_SPLITTER_2x128toNx64;

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------
architecture full of APPLICATION_SPLITTER_2x128toNx64 is

   component tsu_async is
   -- PORTS
   port (
      RESET          : in std_logic;

      -- Input interface
      IN_CLK         : in std_logic;

      IN_TS          : in std_logic_vector(63 downto 0);
      IN_TS_DV       : in std_logic;

      -- Output interface
      OUT_CLK        : in std_logic;

      OUT_TS         : out std_logic_vector(63 downto 0);
      OUT_TS_DV      : out std_logic
   );
   end component tsu_async;

   component FL_TRANSFORMER_128TO64 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- RX interface
      RX_DATA        : in  std_logic_vector(127 downto 0);
      RX_DREM        : in  std_logic_vector(3 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX interface
      TX_DATA        : out std_logic_vector(63 downto 0);
      TX_DREM        : out std_logic_vector(2 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
   end component FL_TRANSFORMER_128TO64;

   component FL_TRANSFORMER_64TO128 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- RX interface
      RX_DATA        : in  std_logic_vector(63 downto 0);
      RX_DREM        : in  std_logic_vector(2 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX interface
      TX_DATA        : out std_logic_vector(127 downto 0);
      TX_DREM        : out std_logic_vector(3 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
   end component FL_TRANSFORMER_64TO128;

component FL_WATCH_2 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(1 downto 0);
      EOF_N          : in std_logic_vector(1 downto 0);
      SOP_N          : in std_logic_vector(1 downto 0);
      EOP_N          : in std_logic_vector(1 downto 0);
      DST_RDY_N      : in std_logic_vector(1 downto 0);
      SRC_RDY_N      : in std_logic_vector(1 downto 0);

      FRAME_ERR      : out std_logic_vector(1 downto 0);

      MI_DWR	      : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	         : in std_logic;
      MI_WR	         : in std_logic;
      MI_BE	         : in std_logic_vector(3 downto 0);
      MI_DRD         : out std_logic_vector(31 downto 0);
      MI_ARDY        : out std_logic;
      MI_DRDY        : out std_logic
   );
end component;

-- ----------------------------------------------------------------------------
--                            Signal declaration
-- ----------------------------------------------------------------------------
   -- -------------------------------------------------------------------------
   --                          Framelink signals
   -- -------------------------------------------------------------------------

   signal trans0_tx_data       : std_logic_vector(64-1 downto 0);
   signal trans0_tx_drem       : std_logic_vector(3-1 downto 0);
   signal trans0_tx_sof_n      : std_logic;
   signal trans0_tx_eof_n      : std_logic;
   signal trans0_tx_sop_n      : std_logic;
   signal trans0_tx_eop_n      : std_logic;
   signal trans0_tx_src_rdy_n  : std_logic;
   signal trans0_tx_dst_rdy_n  : std_logic;

   signal trans1_tx_data       : std_logic_vector(64-1 downto 0);
   signal trans1_tx_drem       : std_logic_vector(3-1 downto 0);
   signal trans1_tx_sof_n      : std_logic;
   signal trans1_tx_eof_n      : std_logic;
   signal trans1_tx_sop_n      : std_logic;
   signal trans1_tx_eop_n      : std_logic;
   signal trans1_tx_src_rdy_n  : std_logic;
   signal trans1_tx_dst_rdy_n  : std_logic;

   signal split0_tx_data       : std_logic_vector(DMA_FLOWS/2*64-1 downto 0);
   signal split0_tx_drem       : std_logic_vector(DMA_FLOWS/2*3-1 downto 0);
   signal split0_tx_sof_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split0_tx_eof_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split0_tx_sop_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split0_tx_eop_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split0_tx_src_rdy_n  : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split0_tx_dst_rdy_n  : std_logic_vector(DMA_FLOWS/2-1 downto 0);

   signal split1_tx_data       : std_logic_vector(DMA_FLOWS/2*64-1 downto 0);
   signal split1_tx_drem       : std_logic_vector(DMA_FLOWS/2*3-1 downto 0);
   signal split1_tx_sof_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split1_tx_eof_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split1_tx_sop_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split1_tx_eop_n      : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split1_tx_src_rdy_n  : std_logic_vector(DMA_FLOWS/2-1 downto 0);
   signal split1_tx_dst_rdy_n  : std_logic_vector(DMA_FLOWS/2-1 downto 0);

   signal split_tx_data       : std_logic_vector(DMA_FLOWS*64-1 downto 0);
   signal split_tx_drem       : std_logic_vector(DMA_FLOWS*3-1 downto 0);
   signal split_tx_sof_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal split_tx_eof_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal split_tx_sop_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal split_tx_eop_n      : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal split_tx_src_rdy_n  : std_logic_vector(DMA_FLOWS-1 downto 0);
   signal split_tx_dst_rdy_n  : std_logic_vector(DMA_FLOWS-1 downto 0);

   -- -------------------------------------------------------------------------
   --                        FrameLink signals
   -- -------------------------------------------------------------------------
   -- signals to FL_WATCH
   signal fl_watch_rx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_watch_rx_dst_rdy_n : std_logic_vector(1 downto 0);

   -- -------------------------------------------------------------------------
   --                         Pacodag signals
   -- -------------------------------------------------------------------------
   signal ts_sync               : std_logic_vector(63 downto 0);
   signal ts_dv_sync            : std_logic;


   signal sIBUF0_TX_DST_RDY_N   : std_logic;
   signal sIBUF1_TX_DST_RDY_N   : std_logic;

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                             FrameLink
   -- -------------------------------------------------------------------------

   -- fl transformer IBUF fl stream 128b -> 64b 

   FL_TRANSFORMER_RX0_I : FL_TRANSFORMER_128TO64
   port map (
       CLK            => CLK,
       RESET          => RESET,

                        -- RX interface
       RX_DATA        => IBUF0_TX_DATA,
       RX_DREM        => IBUF0_TX_REM,
       RX_SOF_N       => IBUF0_TX_SOF_N,
       RX_EOF_N       => IBUF0_TX_EOF_N,
       RX_SOP_N       => IBUF0_TX_SOP_N,
       RX_EOP_N       => IBUF0_TX_EOP_N,
       RX_SRC_RDY_N   => IBUF0_TX_SRC_RDY_N,
       RX_DST_RDY_N   => sIBUF0_TX_DST_RDY_N,

                        -- TX interface
       TX_DATA        => trans0_tx_data,
       TX_DREM        => trans0_tx_drem,
       TX_SOF_N       => trans0_tx_sof_n,
       TX_EOF_N       => trans0_tx_eof_n,
       TX_SOP_N       => trans0_tx_sop_n,
       TX_EOP_N       => trans0_tx_eop_n,
       TX_SRC_RDY_N   => trans0_tx_src_rdy_n,
       TX_DST_RDY_N   => trans0_tx_dst_rdy_n
   );

   FL_TRANSFORMER_RX1_I : FL_TRANSFORMER_128TO64
   port map (
       CLK            => CLK,
       RESET          => RESET,

                        -- RX interface
       RX_DATA        => IBUF1_TX_DATA,
       RX_DREM        => IBUF1_TX_REM,
       RX_SOF_N       => IBUF1_TX_SOF_N,
       RX_EOF_N       => IBUF1_TX_EOF_N,
       RX_SOP_N       => IBUF1_TX_SOP_N,
       RX_EOP_N       => IBUF1_TX_EOP_N,
       RX_SRC_RDY_N   => IBUF1_TX_SRC_RDY_N,
       RX_DST_RDY_N   => sIBUF1_TX_DST_RDY_N,

                        -- TX interface
       TX_DATA        => trans1_tx_data,
       TX_DREM        => trans1_tx_drem,
       TX_SOF_N       => trans1_tx_sof_n,
       TX_EOF_N       => trans1_tx_eof_n,
       TX_SOP_N       => trans1_tx_sop_n,
       TX_EOP_N       => trans1_tx_eop_n,
       TX_SRC_RDY_N   => trans1_tx_src_rdy_n,
       TX_DST_RDY_N   => trans1_tx_dst_rdy_n
   );

   -- fl splitter 64b -> Nx 64b
   FL_SPLITTER_RX0_I: entity work.FL_SPLITTER
   generic map (
      DATA_WIDTH     => 64,
      OUTPUT_COUNT   => DMA_FLOWS/2,
      FRAME_PARTS    => 1
   )
   port map (
       CLK            => CLK,
       RESET          => RESET,

                        -- input interface
       RX_SOF_N       => trans0_tx_sof_n,
       RX_SOP_N       => trans0_tx_sop_n,
       RX_EOP_N       => trans0_tx_eop_n,
       RX_EOF_N       => trans0_tx_eof_n,
       RX_SRC_RDY_N   => trans0_tx_src_rdy_n,
       RX_DST_RDY_N   => trans0_tx_dst_rdy_n,
       RX_DATA        => trans0_tx_data,
       RX_REM         => trans0_tx_drem,

                        -- output interface
       TX_SOF_N       => split0_tx_sof_n,
       TX_SOP_N       => split0_tx_sop_n,
       TX_EOP_N       => split0_tx_eop_n,
       TX_EOF_N       => split0_tx_eof_n,
       TX_SRC_RDY_N   => split0_tx_src_rdy_n,
       TX_DST_RDY_N   => split0_tx_dst_rdy_n,
       TX_DATA        => split0_tx_data,
       TX_REM         => split0_tx_drem
   );

   FL_SPLITTER_RX1_I: entity work.FL_SPLITTER
   generic map (
      DATA_WIDTH     => 64,
      OUTPUT_COUNT   => DMA_FLOWS/2,
      FRAME_PARTS    => 1
   )
   port map (
       CLK            => CLK,
       RESET          => RESET,

                        -- input interface
       RX_SOF_N       => trans1_tx_sof_n,
       RX_SOP_N       => trans1_tx_sop_n,
       RX_EOP_N       => trans1_tx_eop_n,
       RX_EOF_N       => trans1_tx_eof_n,
       RX_SRC_RDY_N   => trans1_tx_src_rdy_n,
       RX_DST_RDY_N   => trans1_tx_dst_rdy_n,
       RX_DATA        => trans1_tx_data,
       RX_REM         => trans1_tx_drem,

                        -- output interface
       TX_SOF_N       => split1_tx_sof_n,
       TX_SOP_N       => split1_tx_sop_n,
       TX_EOP_N       => split1_tx_eop_n,
       TX_EOF_N       => split1_tx_eof_n,
       TX_SRC_RDY_N   => split1_tx_src_rdy_n,
       TX_DST_RDY_N   => split1_tx_dst_rdy_n,
       TX_DATA        => split1_tx_data,
       TX_REM         => split1_tx_drem
   );

   split_tx_data       <= split1_tx_data  & split0_tx_data;
   split_tx_drem       <= split1_tx_drem  & split0_tx_drem;
   split_tx_sof_n      <= split1_tx_sof_n & split0_tx_sof_n;
   split_tx_eof_n      <= split1_tx_eof_n & split0_tx_eof_n;
   split_tx_sop_n      <= split1_tx_sop_n & split0_tx_sop_n;
   split_tx_eop_n      <= split1_tx_eop_n & split0_tx_eop_n;
   split_tx_src_rdy_n  <= split1_tx_src_rdy_n & split0_tx_src_rdy_n;
   split1_tx_dst_rdy_n <= split_tx_dst_rdy_n(DMA_FLOWS-1 downto DMA_FLOWS/2);
   split0_tx_dst_rdy_n <= split_tx_dst_rdy_n(DMA_FLOWS/2-1 downto 0);

   TX_DATA             <= split_tx_data;
   TX_DREM             <= split_tx_drem;
   TX_SOF_N            <= split_tx_sof_n;
   TX_EOF_N            <= split_tx_eof_n;
   TX_SOP_N            <= split_tx_sop_n;
   TX_EOP_N            <= split_tx_eop_n;
   TX_SRC_RDY_N        <= split_tx_src_rdy_n;
   split_tx_dst_rdy_n  <= TX_DST_RDY_N;

   
   -- IB grounging
   IB_DOWN_DST_RDY_N <= '0';
   IB_UP_SRC_RDY_N <= '1';
   IB_UP_SOF_N <= '1';
   IB_UP_EOF_N <= '1';
   IB_UP_DATA <= X"0000000000000000";

   -- FL_WATCH RX (ibuf->application)
   FL_WATCH_RX_I : FL_WATCH_2
   port map(
      CLK       => CLK,
      RESET     => RESET,

      SOF_N     => fl_watch_rx_sof_n,
      EOF_N     => fl_watch_rx_eof_n,
      SOP_N     => fl_watch_rx_sop_n,
      EOP_N     => fl_watch_rx_eop_n,
      DST_RDY_N => fl_watch_rx_dst_rdy_n,
      SRC_RDY_N => fl_watch_rx_src_rdy_n,

      MI_DWR    => MI32_DWR,
      MI_ADDR   => MI32_ADDR,
      MI_RD     => MI32_RD,
      MI_WR     => MI32_WR,
      MI_BE     => MI32_BE,
      MI_DRD    => MI32_DRD,
      MI_ARDY   => MI32_ARDY,
      MI_DRDY   => MI32_DRDY
   );

   fl_watch_rx_sof_n <= IBUF1_TX_SOF_N & IBUF0_TX_SOF_N;
   fl_watch_rx_eof_n <= IBUF1_TX_EOF_N & IBUF0_TX_EOF_N;
   fl_watch_rx_sop_n <= IBUF1_TX_SOP_N & IBUF0_TX_SOP_N;
   fl_watch_rx_eop_n <= IBUF1_TX_EOP_N & IBUF0_TX_EOP_N;
   fl_watch_rx_src_rdy_n <= IBUF1_TX_SRC_RDY_N & IBUF0_TX_SRC_RDY_N;
   fl_watch_rx_dst_rdy_n <= sIBUF1_TX_DST_RDY_N & sIBUF0_TX_DST_RDY_N;

   IBUF0_TX_DST_RDY_N <= sIBUF0_TX_DST_RDY_N;
   IBUF1_TX_DST_RDY_N <= sIBUF1_TX_DST_RDY_N;
   -- -------------------------------------------------------------------------
   --                              PACODAG
   -- -------------------------------------------------------------------------
   PACODAG_TOP_I: entity work.pacodag_tsu_top2_128b_norec
   generic map(
      HEADER_EN => PACODAG_HEADER_EN,
      FOOTER_EN => PACODAG_FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD0_CTRL_CLK              => IBUF0_CTRL_CLK,
      PCD0_CTRL_DATA             => IBUF0_CTRL_DATA,
      PCD0_CTRL_REM              => IBUF0_CTRL_REM,
      PCD0_CTRL_SRC_RDY_N        => IBUF0_CTRL_SRC_RDY_N,
      PCD0_CTRL_SOP_N            => IBUF0_CTRL_SOP_N,
      PCD0_CTRL_EOP_N            => IBUF0_CTRL_EOP_N,
      PCD0_CTRL_DST_RDY_N        => IBUF0_CTRL_DST_RDY_N,
      PCD0_CTRL_RDY              => IBUF0_CTRL_RDY,
      PCD0_SOP                   => IBUF0_SOP,
      PCD0_STAT_PAYLOAD_LEN      => IBUF0_PAYLOAD_LEN,
      PCD0_STAT_FRAME_ERROR      => IBUF0_FRAME_ERROR,
      PCD0_STAT_CRC_CHECK_FAILED => IBUF0_CRC_CHECK_FAILED,
      PCD0_STAT_MAC_CHECK_FAILED => IBUF0_MAC_CHECK_FAILED,
      PCD0_STAT_LEN_BELOW_MIN    => IBUF0_LEN_BELOW_MIN,
      PCD0_STAT_LEN_OVER_MTU     => IBUF0_LEN_OVER_MTU,
      PCD0_STAT_DV               => IBUF0_STAT_DV,

      PCD1_CTRL_CLK              => IBUF1_CTRL_CLK,
      PCD1_CTRL_DATA             => IBUF1_CTRL_DATA,
      PCD1_CTRL_REM              => IBUF1_CTRL_REM,
      PCD1_CTRL_SRC_RDY_N        => IBUF1_CTRL_SRC_RDY_N,
      PCD1_CTRL_SOP_N            => IBUF1_CTRL_SOP_N,
      PCD1_CTRL_EOP_N            => IBUF1_CTRL_EOP_N,
      PCD1_CTRL_DST_RDY_N        => IBUF1_CTRL_DST_RDY_N,
      PCD1_CTRL_RDY              => IBUF1_CTRL_RDY,
      PCD1_SOP                   => IBUF1_SOP,
      PCD1_STAT_PAYLOAD_LEN      => IBUF1_PAYLOAD_LEN,
      PCD1_STAT_FRAME_ERROR      => IBUF1_FRAME_ERROR,
      PCD1_STAT_CRC_CHECK_FAILED => IBUF1_CRC_CHECK_FAILED,
      PCD1_STAT_MAC_CHECK_FAILED => IBUF1_MAC_CHECK_FAILED,
      PCD1_STAT_LEN_BELOW_MIN    => IBUF1_LEN_BELOW_MIN,
      PCD1_STAT_LEN_OVER_MTU     => IBUF1_LEN_OVER_MTU,
      PCD1_STAT_DV               => IBUF1_STAT_DV,

      TS       => ts_sync,
      TS_DV    => ts_dv_sync
   );

   -- ---------------------------------------------------------------
   -- Generate tsu_async only if timestamp unit is also generated
   ts_true_async : if TIMESTAMP_UNIT = true generate
      tsu_async_i : tsu_async
      -- PORTS
      port map (
         RESET          => RESET,

         -- Input interface
         IN_CLK         => TS_CLK,

         IN_TS          => TS,
         IN_TS_DV       => TS_DV,

         -- Output interface
         OUT_CLK        => IBUF0_CTRL_CLK,

         OUT_TS         => ts_sync,
         OUT_TS_DV      => ts_dv_sync
      );
   end generate ts_true_async;

   -- Else map TS and TS_DV signals directly into pacodag
   ts_false_async : if TIMESTAMP_UNIT = false generate
      ts_sync <= TS;
      ts_dv_sync <= TS_DV;
   end generate ts_false_async;
   -- ---------------------------------------------------------------

end architecture full;
