
-- aurvc_core.vhd: Aurora IP core entity
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

entity rio_aurora_module is
    generic (                    
         LANES             : integer;     -- Number of lanes 
         DATA_PATHS        : integer      -- Number of data paths
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to (DATA_PATHS*8)-1);
            TX_REM           : in std_logic_vector(0 to log2(DATA_PATHS)-1);
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to (DATA_PATHS*8)-1);
            RX_REM           : out std_logic_vector(0 to log2(DATA_PATHS)-1);
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

            UFC_RX_DATA      : out std_logic_vector(0 to (DATA_PATHS*8)-1);
            UFC_RX_REM       : out std_logic_vector(0 to log2(DATA_PATHS)-1);
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXN            : in  std_logic_vector(0 to LANES-1);
            RXP            : in  std_logic_vector(0 to LANES-1);

            TXN            : out std_logic_vector(0 to LANES-1);
            TXP            : out std_logic_vector(0 to LANES-1);

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic_vector(0 to LANES-1);

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

end rio_aurora_module;
