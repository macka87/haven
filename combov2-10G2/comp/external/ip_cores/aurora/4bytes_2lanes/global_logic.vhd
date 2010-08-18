--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: global_logic.vhd,v $
--          Rev:  $Revision$
--
--      Company:  Xilinx
-- Contributors:  R. K. Awalt, B. L. Woodard, N. Gulstone
--
--   Disclaimer:  XILINX IS PROVIDING THIS DESIGN, CODE, OR
--                INFORMATION "AS IS" SOLELY FOR USE IN DEVELOPING
--                PROGRAMS AND SOLUTIONS FOR XILINX DEVICES.  BY
--                PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
--                ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
--                APPLICATION OR STANDARD, XILINX IS MAKING NO
--                REPRESENTATION THAT THIS IMPLEMENTATION IS FREE
--                FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE
--                RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY
--                REQUIRE FOR YOUR IMPLEMENTATION.  XILINX
--                EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH
--                RESPECT TO THE ADEQUACY OF THE IMPLEMENTATION,
--                INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
--                REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
--                FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES
--                OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
--                PURPOSE.
--
--                (c) Copyright 2004 Xilinx, Inc.
--                All rights reserved.
--

--
--  GLOBAL_LOGIC
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: The GLOBAL_LOGIC module handles channel bonding, channel
--               verification, channel error manangement and idle generation.
--
--               This module supports 2 2-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_4byte2lane;

entity GLOBAL_LOGIC is
    generic (
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- MGT Interface

            CH_BOND_DONE       : in std_logic_vector(0 to 1);
            EN_CHAN_SYNC       : out std_logic;

    -- Aurora Lane Interface

            LANE_UP            : in std_logic_vector(0 to 1);
            SOFT_ERROR         : in std_logic_vector(0 to 1);
            HARD_ERROR         : in std_logic_vector(0 to 1);
            CHANNEL_BOND_LOAD  : in std_logic_vector(0 to 1);
            GOT_A              : in std_logic_vector(0 to 3);
            GOT_V              : in std_logic_vector(0 to 1);
            GEN_A              : out std_logic_vector(0 to 1);
            GEN_K              : out std_logic_vector(0 to 3);
            GEN_R              : out std_logic_vector(0 to 3);
            GEN_V              : out std_logic_vector(0 to 3);
            RESET_LANES        : out std_logic_vector(0 to 1);

    -- System Interface

            USER_CLK           : in std_logic;
            RESET              : in std_logic;
            POWER_DOWN         : in std_logic;
            CHANNEL_UP         : out std_logic;
            START_RX           : out std_logic;
            CHANNEL_SOFT_ERROR : out std_logic;
            CHANNEL_HARD_ERROR : out std_logic

         );

end GLOBAL_LOGIC;

architecture MAPPED of GLOBAL_LOGIC is

-- External Register Declarations --

    signal EN_CHAN_SYNC_Buffer       : std_logic;
    signal GEN_A_Buffer              : std_logic_vector(0 to 1);
    signal GEN_K_Buffer              : std_logic_vector(0 to 3);
    signal GEN_R_Buffer              : std_logic_vector(0 to 3);
    signal GEN_V_Buffer              : std_logic_vector(0 to 3);
    signal RESET_LANES_Buffer        : std_logic_vector(0 to 1);
    signal CHANNEL_UP_Buffer         : std_logic;
    signal START_RX_Buffer           : std_logic;
    signal CHANNEL_SOFT_ERROR_Buffer : std_logic;
    signal CHANNEL_HARD_ERROR_Buffer : std_logic;

-- Wire Declarations --

    signal gen_ver_i       : std_logic;
    signal reset_channel_i : std_logic;
    signal did_ver_i       : std_logic;

-- Component Declarations --

    component CHANNEL_INIT_SM
        generic (
                EXTEND_WATCHDOGS  : boolean := FALSE
        );
        port (

        -- MGT Interface

                CH_BOND_DONE      : in std_logic_vector(0 to 1);
                EN_CHAN_SYNC      : out std_logic;

        -- Aurora Lane Interface

                CHANNEL_BOND_LOAD : in std_logic_vector(0 to 1);
                GOT_A             : in std_logic_vector(0 to 3);
                GOT_V             : in std_logic_vector(0 to 1);
                RESET_LANES       : out std_logic_vector(0 to 1);

        -- System Interface

                USER_CLK          : in std_logic;
                RESET             : in std_logic;
                CHANNEL_UP        : out std_logic;
                START_RX          : out std_logic;

        -- Idle and Verification Sequence Generator Interface

                DID_VER           : in std_logic;
                GEN_VER           : out std_logic;

        -- Channel Init State Machine Interface

                RESET_CHANNEL     : in std_logic

             );

    end component;


    component IDLE_AND_VER_GEN

        port (

        -- Channel Init SM Interface

                GEN_VER  : in std_logic;
                DID_VER  : out std_logic;

        -- Aurora Lane Interface

                GEN_A    : out std_logic_vector(0 to 1);
                GEN_K    : out std_logic_vector(0 to 3);
                GEN_R    : out std_logic_vector(0 to 3);
                GEN_V    : out std_logic_vector(0 to 3);

        -- System Interface

                RESET    : in std_logic;
                USER_CLK : in std_logic

             );

    end component;


    component CHANNEL_ERROR_DETECT

        port (

        -- Aurora Lane Interface

                SOFT_ERROR         : in std_logic_vector(0 to 1);
                HARD_ERROR         : in std_logic_vector(0 to 1);
                LANE_UP            : in std_logic_vector(0 to 1);

        -- System Interface

                USER_CLK           : in std_logic;
                POWER_DOWN         : in std_logic;

                CHANNEL_SOFT_ERROR : out std_logic;
                CHANNEL_HARD_ERROR : out std_logic;

        -- Channel Init SM Interface

                RESET_CHANNEL      : out std_logic

             );

    end component;

begin

    EN_CHAN_SYNC       <= EN_CHAN_SYNC_Buffer;
    GEN_A              <= GEN_A_Buffer;
    GEN_K              <= GEN_K_Buffer;
    GEN_R              <= GEN_R_Buffer;
    GEN_V              <= GEN_V_Buffer;
    RESET_LANES        <= RESET_LANES_Buffer;
    CHANNEL_UP         <= CHANNEL_UP_Buffer;
    START_RX           <= START_RX_Buffer;
    CHANNEL_SOFT_ERROR <= CHANNEL_SOFT_ERROR_Buffer;
    CHANNEL_HARD_ERROR <= CHANNEL_HARD_ERROR_Buffer;

-- Main Body of Code --

    -- State Machine for channel bonding and verification.

    channel_init_sm_i : CHANNEL_INIT_SM
        generic map (
                    EXTEND_WATCHDOGS => EXTEND_WATCHDOGS
        )
        port map (

        -- MGT Interface

                    CH_BOND_DONE => CH_BOND_DONE,
                    EN_CHAN_SYNC => EN_CHAN_SYNC_Buffer,

        -- Aurora Lane Interface

                    CHANNEL_BOND_LOAD => CHANNEL_BOND_LOAD,
                    GOT_A => GOT_A,
                    GOT_V => GOT_V,
                    RESET_LANES => RESET_LANES_Buffer,

        -- System Interface

                    USER_CLK => USER_CLK,
                    RESET => RESET,
                    START_RX => START_RX_Buffer,
                    CHANNEL_UP => CHANNEL_UP_Buffer,

        -- Idle and Verification Sequence Generator Interface

                    DID_VER => did_ver_i,
                    GEN_VER => gen_ver_i,

        -- Channel Error Management Module Interface

                    RESET_CHANNEL => reset_channel_i

                 );


    -- Idle and verification sequence generator module.

    idle_and_ver_gen_i : IDLE_AND_VER_GEN

        port map (

        -- Channel Init SM Interface

                    GEN_VER => gen_ver_i,
                    DID_VER => did_ver_i,

        -- Aurora Lane Interface

                    GEN_A => GEN_A_Buffer,
                    GEN_K => GEN_K_Buffer,
                    GEN_R => GEN_R_Buffer,
                    GEN_V => GEN_V_Buffer,

        -- System Interface

                    RESET => RESET,
                    USER_CLK => USER_CLK

                 );



    -- Channel Error Management module.

    channel_error_detect_i : CHANNEL_ERROR_DETECT

        port map (

        -- Aurora Lane Interface

                    SOFT_ERROR => SOFT_ERROR,
                    HARD_ERROR => HARD_ERROR,
                    LANE_UP => LANE_UP,

        -- System Interface

                    USER_CLK => USER_CLK,
                    POWER_DOWN => POWER_DOWN,
                    CHANNEL_SOFT_ERROR => CHANNEL_SOFT_ERROR_Buffer,
                    CHANNEL_HARD_ERROR => CHANNEL_HARD_ERROR_Buffer,

        -- Channel Init State Machine Interface

                    RESET_CHANNEL => reset_channel_i

                 );

end MAPPED;
