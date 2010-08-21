-- aurvc_core.vhd: Aurora IP core full architecture
-- Copyright (C) 2007 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
-- 
-- TODO: - 

library IEEE;
use IEEE.STD_LOGIC_1164.all;

-- synthesis translate_off
library UNISIM;
use UNISIM.Vcomponents.ALL; 
-- synthesis translate_on
use work.math_pack.all; 
library aurora_2byte;
library aurora_4byte1lane;
library aurora_4byte2lane;
library aurora_8byte;

architecture MAPPED of rio_aurora_module is
component aurora_2bytes_1lane is
    generic (                    
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to 15);
            TX_REM           : in std_logic;
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to 15);
            RX_REM           : out std_logic;
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Native Flow Control Interface

            NFC_REQ_N        : in std_logic;
            NFC_NB           : in std_logic_vector(0 to 3);
            NFC_ACK_N        : out std_logic;

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     : in std_logic;
            UFC_TX_MS        : in std_logic_vector(0 to 2);
            UFC_TX_ACK_N     : out std_logic;

    -- User Flow Control RX Inteface

            UFC_RX_DATA      : out std_logic_vector(0 to 15);
            UFC_RX_REM       : out std_logic;
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXP              : in std_logic;
            RXN              : in std_logic;

            TXP              : out std_logic;
            TXN              : out std_logic;

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic;

    -- Clock Compensation Control Interface

            WARN_CC          : in std_logic;
            DO_CC            : in std_logic;

    -- System Interface

            DCM_NOT_LOCKED   : in std_logic;
            USER_CLK         : in std_logic;
            RESET            : in std_logic;
            POWER_DOWN       : in std_logic;
            LOOPBACK         : in std_logic_vector(1 downto 0)

         );

end component;

component aurora_4bytes_1lane is
    generic (                    
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to 31);
            TX_REM           : in std_logic_vector(0 to 1);
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to 31);
            RX_REM           : out std_logic_vector(0 to 1);
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Native Flow Control Interface

            NFC_REQ_N        : in std_logic;
            NFC_NB           : in std_logic_vector(0 to 3);
            NFC_ACK_N        : out std_logic;

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     : in std_logic;
            UFC_TX_MS        : in std_logic_vector(0 to 2);
            UFC_TX_ACK_N     : out std_logic;

    -- User Flow Control RX Inteface

            UFC_RX_DATA      : out std_logic_vector(0 to 31);
            UFC_RX_REM       : out std_logic_vector(0 to 1);
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXP              : in std_logic;
            RXN              : in std_logic;
            TXP              : out std_logic;
            TXN              : out std_logic;

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic;

    -- Clock Compensation Control Interface

            WARN_CC          : in std_logic;
            DO_CC            : in std_logic;

    -- System Interface

            DCM_NOT_LOCKED   : in std_logic;
            USER_CLK         : in std_logic;
            USER_CLK_N_2X    : in std_logic;
            RESET            : in std_logic;
            POWER_DOWN       : in std_logic;
            LOOPBACK         : in std_logic_vector(1 downto 0)

         );

end component;

component aurora_4bytes_2lanes is
    generic (                    
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to 31);
            TX_REM           : in std_logic_vector(0 to 1);
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to 31);
            RX_REM           : out std_logic_vector(0 to 1);
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Native Flow Control Interface

            NFC_REQ_N        : in std_logic;
            NFC_NB           : in std_logic_vector(0 to 3);
            NFC_ACK_N        : out std_logic;

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     : in std_logic;
            UFC_TX_MS        : in std_logic_vector(0 to 2);
            UFC_TX_ACK_N     : out std_logic;

    -- User Flow Control RX Inteface

            UFC_RX_DATA      : out std_logic_vector(0 to 31);
            UFC_RX_REM       : out std_logic_vector(0 to 1);
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXP              : in std_logic_vector(0 to 1);
            RXN              : in std_logic_vector(0 to 1);

            TXP              : out std_logic_vector(0 to 1);
            TXN              : out std_logic_vector(0 to 1);

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic_vector(0 to 1);

    -- Clock Compensation Control Interface

            WARN_CC          : in std_logic;
            DO_CC            : in std_logic;

    -- System Interface

            DCM_NOT_LOCKED   : in std_logic;
            USER_CLK         : in std_logic;
            RESET            : in std_logic;
            POWER_DOWN       : in std_logic;
            LOOPBACK         : in std_logic_vector(1 downto 0)

         );

end component;

component aurora_8bytes_2lanes is
    generic (                    
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to 63);
            TX_REM           : in std_logic_vector(0 to 2);
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to 63);
            RX_REM           : out std_logic_vector(0 to 2);
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Native Flow Control Interface

            NFC_REQ_N        : in std_logic;
            NFC_NB           : in std_logic_vector(0 to 3);
            NFC_ACK_N        : out std_logic;

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     : in std_logic;
            UFC_TX_MS        : in std_logic_vector(0 to 2);
            UFC_TX_ACK_N     : out std_logic;

    -- User Flow Control RX Inteface

            UFC_RX_DATA      : out std_logic_vector(0 to 63);
            UFC_RX_REM       : out std_logic_vector(0 to 2);
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXP              : in std_logic_vector(0 to 1);
            RXN              : in std_logic_vector(0 to 1);
            TXP              : out std_logic_vector(0 to 1);
            TXN              : out std_logic_vector(0 to 1);

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic_vector(0 to 1);

    -- Clock Compensation Control Interface

            WARN_CC          : in std_logic;
            DO_CC            : in std_logic;

    -- System Interface

            DCM_NOT_LOCKED   : in std_logic;
            USER_CLK         : in std_logic;
            USER_CLK_N_2X    : in std_logic;
            RESET            : in std_logic;
            POWER_DOWN       : in std_logic;
            LOOPBACK         : in std_logic_vector(1 downto 0)

         );

end component;

begin

gen_2bytes_1lane: if (LANES = 1 and DATA_PATHS = 2) generate

aurora_2bytes_1lane_u: aurora_2bytes_1lane
    generic map(                    
            EXTEND_WATCHDOGS   => false
    )
    port map(

    -- LocalLink TX Interface

            TX_D             => TX_D,
            TX_REM           => TX_REM(0),
            TX_SRC_RDY_N     => TX_SRC_RDY_N,
            TX_SOF_N         => TX_SOF_N,
            TX_EOF_N         => TX_EOF_N,
            TX_DST_RDY_N     => TX_DST_RDY_N,

    -- LocalLink RX Interface

            RX_D             => RX_D,
            RX_REM           => RX_REM(0),
            RX_SRC_RDY_N     => RX_SRC_RDY_N,
            RX_SOF_N         => RX_SOF_N,
            RX_EOF_N         => RX_EOF_N,

    -- Native Flow Control Interface

            NFC_REQ_N        => NFC_REQ_N,
            NFC_NB           => NFC_NB,
            NFC_ACK_N        => NFC_ACK_N,

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     => UFC_TX_REQ_N,
            UFC_TX_MS        => UFC_TX_MS,
            UFC_TX_ACK_N     => UFC_TX_ACK_N,

    -- User Flow Control RX Inteface

            UFC_RX_DATA      => UFC_RX_DATA,
            UFC_RX_REM       => UFC_RX_REM(0),
            UFC_RX_SRC_RDY_N => UFC_RX_SRC_RDY_N,
            UFC_RX_SOF_N     => UFC_RX_SOF_N,
            UFC_RX_EOF_N     => UFC_RX_EOF_N,

    -- MGT Serial I/O

            RXP              => RXP(0),
            RXN              => RXN(0),

            TXP              => TXP(0),
            TXN              => TXN(0),

    -- MGT Reference Clock Interface

            TOP_REF_CLK     => TOP_REF_CLK,

    -- Error Detection Interface

            HARD_ERROR       => HARD_ERROR,
            SOFT_ERROR       => SOFT_ERROR,
            FRAME_ERROR      => FRAME_ERROR,

    -- Status

            CHANNEL_UP       => CHANNEL_UP,
            LANE_UP          => LANE_UP(0),

    -- Clock Compensation Control Interface

            WARN_CC          => WARN_CC,
            DO_CC            => DO_CC,

    -- System Interface

            DCM_NOT_LOCKED   => DCM_NOT_LOCKED,
            USER_CLK         => USER_CLK,
            RESET            => RESET,
            POWER_DOWN       => POWER_DOWN,
            LOOPBACK         => LOOPBACK
         );
end generate;

gen_4bytes_1lane: if (LANES = 1 and DATA_PATHS = 4) generate

aurora_4bytes_1lane_u: aurora_4bytes_1lane
    generic map(                    
            EXTEND_WATCHDOGS   => false
    )
    port map(

    -- LocalLink TX Interface

            TX_D             => TX_D,
            TX_REM           => TX_REM,
            TX_SRC_RDY_N     => TX_SRC_RDY_N,
            TX_SOF_N         => TX_SOF_N,
            TX_EOF_N         => TX_EOF_N,
            TX_DST_RDY_N     => TX_DST_RDY_N,

    -- LocalLink RX Interface

            RX_D             => RX_D,
            RX_REM           => RX_REM,
            RX_SRC_RDY_N     => RX_SRC_RDY_N,
            RX_SOF_N         => RX_SOF_N,
            RX_EOF_N         => RX_EOF_N,

    -- Native Flow Control Interface

            NFC_REQ_N        => NFC_REQ_N,
            NFC_NB           => NFC_NB,
            NFC_ACK_N        => NFC_ACK_N,

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     => UFC_TX_REQ_N,
            UFC_TX_MS        => UFC_TX_MS,
            UFC_TX_ACK_N     => UFC_TX_ACK_N,

    -- User Flow Control RX Inteface

            UFC_RX_DATA      => UFC_RX_DATA,
            UFC_RX_REM       => UFC_RX_REM,
            UFC_RX_SRC_RDY_N => UFC_RX_SRC_RDY_N,
            UFC_RX_SOF_N     => UFC_RX_SOF_N,
            UFC_RX_EOF_N     => UFC_RX_EOF_N,

    -- MGT Serial I/O

            RXP              => RXP(0),
            RXN              => RXN(0),
            TXP              => TXP(0),
            TXN              => TXN(0),

    -- MGT Reference Clock Interface

            TOP_REF_CLK     => TOP_REF_CLK,

    -- Error Detection Interface

            HARD_ERROR       => HARD_ERROR,
            SOFT_ERROR       => SOFT_ERROR,
            FRAME_ERROR      => FRAME_ERROR,

    -- Status

            CHANNEL_UP       => CHANNEL_UP,
            LANE_UP          => LANE_UP(0),

    -- Clock Compensation Control Interface

            WARN_CC          => WARN_CC,
            DO_CC            => DO_CC,

    -- System Interface

            DCM_NOT_LOCKED   => DCM_NOT_LOCKED,
            USER_CLK         => USER_CLK,
            USER_CLK_N_2X    => USER_CLK_N_2X,
            RESET            => RESET,
            POWER_DOWN       => POWER_DOWN,
            LOOPBACK         => LOOPBACK
         );

end generate;

gen_4bytes_2lanes: if (LANES = 2 and DATA_PATHS = 4) generate

aurora_4bytes_2lanes_u: aurora_4bytes_2lanes
    generic map(                    
            EXTEND_WATCHDOGS   => false
    )
    port map(

    -- LocalLink TX Interface

            TX_D             => tx_d,
            TX_REM           => tx_rem,
            TX_SRC_RDY_N     => tx_src_rdy_n,
            TX_SOF_N         => tx_sof_n,
            TX_EOF_N         => tx_eof_n,
            TX_DST_RDY_N     => tx_dst_rdy_n,

    -- LocalLink RX Interface

            RX_D             => rx_d,
            RX_REM           => rx_rem,
            RX_SRC_RDY_N     => rx_src_rdy_n,
            RX_SOF_N         => rx_sof_n,
            RX_EOF_N         => rx_eof_n,

    -- Native Flow Control Interface

            NFC_REQ_N        => nfc_req_n,
            NFC_NB           => nfc_nb,
            NFC_ACK_N        => nfc_ack_n,

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     => ufc_tx_req_n,
            UFC_TX_MS        => ufc_tx_ms,
            UFC_TX_ACK_N     => ufc_tx_ack_n,

    -- User Flow Control RX Inteface

            UFC_RX_DATA      => ufc_rx_data,
            UFC_RX_REM       => ufc_rx_rem,
            UFC_RX_SRC_RDY_N => ufc_rx_src_rdy_n,
            UFC_RX_SOF_N     => ufc_rx_sof_n,
            UFC_RX_EOF_N     => ufc_rx_eof_n,

    -- MGT Serial I/O

            RXP              => rxp,
            RXN              => rxn,

            TXP              => txp,
            TXN              => txn,

    -- MGT Reference Clock Interface

            TOP_REF_CLK     => top_ref_clk,

    -- Error Detection Interface

            HARD_ERROR       => hard_error,
            SOFT_ERROR       => soft_error,
            FRAME_ERROR      => frame_error,

    -- Status

            CHANNEL_UP       => channel_up,
            LANE_UP          => lane_up,

    -- Clock Compensation Control Interface

            WARN_CC          => warn_cc,
            DO_CC            => do_cc,

    -- System Interface

            DCM_NOT_LOCKED   => dcm_not_locked,
            USER_CLK         => user_clk,
            RESET            => reset,
            POWER_DOWN       => power_down,
            LOOPBACK         => loopback

         );

end generate;

gen_8bytes_2lanes: if (LANES = 2 and DATA_PATHS = 8) generate

aurora_8bytes_2lanes_u: aurora_8bytes_2lanes
    generic map(                    
            EXTEND_WATCHDOGS   => false
    )
    port map(

    -- LocalLink TX Interface

            TX_D             => tx_d,
            TX_REM           => tx_rem,
            TX_SRC_RDY_N     => tx_src_rdy_n,
            TX_SOF_N         => tx_sof_n,
            TX_EOF_N         => tx_eof_n,
            TX_DST_RDY_N     => tx_dst_rdy_n,

    -- LocalLink RX Interface

            RX_D             => rx_d,
            RX_REM           => rx_rem,
            RX_SRC_RDY_N     => rx_src_rdy_n,
            RX_SOF_N         => rx_sof_n,
            RX_EOF_N         => rx_eof_n,

    -- Native Flow Control Interface

            NFC_REQ_N        => nfc_req_n,
            NFC_NB           => nfc_nb,
            NFC_ACK_N        => nfc_ack_n,

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     => ufc_tx_req_n,
            UFC_TX_MS        => ufc_tx_ms,
            UFC_TX_ACK_N     => ufc_tx_ack_n,

    -- User Flow Control RX Inteface

            UFC_RX_DATA      => ufc_rx_data,
            UFC_RX_REM       => ufc_rx_rem,
            UFC_RX_SRC_RDY_N => ufc_rx_src_rdy_n,
            UFC_RX_SOF_N     => ufc_rx_sof_n,
            UFC_RX_EOF_N     => ufc_rx_eof_n,

    -- MGT Serial I/O

            RXP              => rxp,
            RXN              => rxn,
            TXP              => txp,
            TXN              => txn,

    -- MGT Reference Clock Interface

            TOP_REF_CLK     => top_ref_clk,

    -- Error Detection Interface

            HARD_ERROR       => hard_error,
            SOFT_ERROR       => soft_error,
            FRAME_ERROR      => frame_error,

    -- Status

            CHANNEL_UP       => channel_up,
            LANE_UP          => lane_up,

    -- Clock Compensation Control Interface

            WARN_CC          => warn_cc,
            DO_CC            => do_cc,

    -- System Interface

            DCM_NOT_LOCKED   => dcm_not_locked,
            USER_CLK         => user_clk,
            USER_CLK_N_2X    => user_clk_n_2x,
            RESET            => reset,
            POWER_DOWN       => power_down,
            LOOPBACK         => loopback

         );

end generate;

end MAPPED;

configuration rio_aurora_module_conf of rio_aurora_module is
   for MAPPED
      for gen_2bytes_1lane
         for aurora_2bytes_1lane_u: aurora_2bytes_1lane 
            use entity aurora_2byte.aurora_2bytes_1lane;
         end for;
      end for;
      for gen_4bytes_1lane
         for aurora_4bytes_1lane_u: aurora_4bytes_1lane 
            use entity aurora_4byte1lane.aurora_4bytes_1lane;
         end for;
      end for;
      for gen_4bytes_2lanes
         for aurora_4bytes_2lanes_u: aurora_4bytes_2lanes 
            use entity aurora_4byte2lane.aurora_4bytes_2lanes;
         end for;
      end for;
      for gen_8bytes_2lanes
         for aurora_8bytes_2lanes_u: aurora_8bytes_2lanes 
            use entity aurora_8byte.aurora_8bytes_2lanes;
         end for;
      end for;
   end for;
end configuration;

