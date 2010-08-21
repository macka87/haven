--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: tx_ll.vhd,v $
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
--  TX_LL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  Description: The TX_LL module converts user data from the LocalLink interface
--               to Aurora Data, then sends it to the Aurora Channel for transmission.
--               It also handles NFC and UFC messages.
--
--               This module supports 4 4-byte lane designs
--
--               This module supports User Flow Control
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity TX_LL is

    port (

    -- LocalLink PDU Interface

            TX_D           : in std_logic_vector(0 to 63);
            TX_REM         : in std_logic_vector(0 to 2);
            TX_SRC_RDY_N   : in std_logic;
            TX_SOF_N       : in std_logic;
            TX_EOF_N       : in std_logic;
            TX_DST_RDY_N   : out std_logic;

    -- UFC Interface

            UFC_TX_REQ_N   : in std_logic;
            UFC_TX_MS      : in std_logic_vector(0 to 3);
            UFC_TX_ACK_N   : out std_logic;

    -- Clock Compensation Interface

            WARN_CC        : in std_logic;
            DO_CC          : in std_logic;

    -- Global Logic Interface

            CHANNEL_UP     : in std_logic;

    -- Aurora Lane Interface

            GEN_SCP        : out std_logic;
            GEN_ECP        : out std_logic;
            GEN_SUF        : out std_logic;
            FC_NB          : out std_logic_vector(0 to 3);
            TX_PE_DATA_V   : out std_logic_vector(0 to 3);
            GEN_PAD        : out std_logic_vector(0 to 3);
            TX_PE_DATA     : out std_logic_vector(0 to 63);
            GEN_CC         : out std_logic_vector(0 to 1);

    -- System Interface

            USER_CLK       : in std_logic

         );

end TX_LL;

architecture MAPPED of TX_LL is

-- External Register Declarations --

    signal TX_DST_RDY_N_Buffer  : std_logic;
    signal UFC_TX_ACK_N_Buffer  : std_logic;
    signal GEN_SCP_Buffer       : std_logic;
    signal GEN_ECP_Buffer       : std_logic;
    signal GEN_SUF_Buffer       : std_logic;
    signal FC_NB_Buffer         : std_logic_vector(0 to 3);
    signal TX_PE_DATA_V_Buffer  : std_logic_vector(0 to 3);
    signal GEN_PAD_Buffer       : std_logic_vector(0 to 3);
    signal TX_PE_DATA_Buffer    : std_logic_vector(0 to 63);
    signal GEN_CC_Buffer        : std_logic_vector(0 to 1);

-- Wire Declarations --

    signal halt_c_i       : std_logic;
    signal tx_dst_rdy_n_i : std_logic;
    signal ufc_message_i  : std_logic_vector(0 to 3);

-- Component Declarations --

    component TX_LL_DATAPATH

        port (

        -- LocalLink PDU Interface

                TX_D         : in std_logic_vector(0 to 63);
                TX_REM       : in std_logic_vector(0 to 2);
                TX_SRC_RDY_N : in std_logic;
                TX_SOF_N     : in std_logic;
                TX_EOF_N     : in std_logic;

        -- Aurora Lane Interface

                TX_PE_DATA_V : out std_logic_vector(0 to 3);
                GEN_PAD      : out std_logic_vector(0 to 3);
                TX_PE_DATA   : out std_logic_vector(0 to 63);

        -- TX_LL Control Module Interface

                HALT_C       : in std_logic;
                TX_DST_RDY_N : in std_logic;
                UFC_MESSAGE  : in std_logic_vector(0 to 3);

        -- System Interface

                CHANNEL_UP   : in std_logic;
                USER_CLK     : in std_logic

             );

    end component;


    component TX_LL_CONTROL

        port (

        -- LocalLink PDU Interface

                TX_SRC_RDY_N  : in std_logic;
                TX_SOF_N      : in std_logic;
                TX_EOF_N      : in std_logic;
                TX_REM        : in std_logic_vector(0 to 2);
                TX_DST_RDY_N  : out std_logic;

        -- UFC Interface

                UFC_TX_REQ_N  : in std_logic;
                UFC_TX_MS     : in std_logic_vector(0 to 3);
                UFC_TX_ACK_N  : out std_logic;

        -- Clock Compensation Interface

                WARN_CC       : in std_logic;
                DO_CC         : in std_logic;

        -- Global Logic Interface

                CHANNEL_UP    : in std_logic;

        -- TX_LL Control Module Interface

                HALT_C        : out std_logic;
                UFC_MESSAGE   : out std_logic_vector(0 to 3);

        -- Aurora Lane Interface

                GEN_SCP       : out std_logic;
                GEN_ECP       : out std_logic;
                GEN_SUF       : out std_logic;
                FC_NB         : out std_logic_vector(0 to 3);
                GEN_CC        : out std_logic_vector(0 to 1);

        -- System Interface

                USER_CLK      : in std_logic

             );

    end component;

begin

    TX_DST_RDY_N  <= TX_DST_RDY_N_Buffer;
    UFC_TX_ACK_N  <= UFC_TX_ACK_N_Buffer;
    GEN_SCP       <= GEN_SCP_Buffer;
    GEN_ECP       <= GEN_ECP_Buffer;
    GEN_SUF       <= GEN_SUF_Buffer;
    FC_NB         <= FC_NB_Buffer;
    TX_PE_DATA_V  <= TX_PE_DATA_V_Buffer;
    GEN_PAD       <= GEN_PAD_Buffer;
    TX_PE_DATA    <= TX_PE_DATA_Buffer;
    GEN_CC        <= GEN_CC_Buffer;

-- Main Body of Code --

    -- TX_DST_RDY_N is generated by TX_LL_CONTROL and used by TX_LL_DATAPATH and
    -- external modules to regulate incoming pdu data signals.

    TX_DST_RDY_N_Buffer <= tx_dst_rdy_n_i;


    -- TX_LL_Datapath module

    tx_ll_datapath_i : TX_LL_DATAPATH

        port map (

        -- LocalLink PDU Interface

                    TX_D => TX_D,
                    TX_REM => TX_REM,
                    TX_SRC_RDY_N => TX_SRC_RDY_N,
                    TX_SOF_N => TX_SOF_N,
                    TX_EOF_N => TX_EOF_N,

        -- Aurora Lane Interface

                    TX_PE_DATA_V => TX_PE_DATA_V_Buffer,
                    GEN_PAD => GEN_PAD_Buffer,
                    TX_PE_DATA => TX_PE_DATA_Buffer,

        -- TX_LL Control Module Interface

                    HALT_C => halt_c_i,
                    TX_DST_RDY_N => tx_dst_rdy_n_i,
                    UFC_MESSAGE => ufc_message_i,

        -- System Interface

                    CHANNEL_UP => CHANNEL_UP,
                    USER_CLK => USER_CLK

                 );


    -- TX_LL_Control module

    tx_ll_control_i : TX_LL_CONTROL

        port map (

        -- LocalLink PDU Interface

                    TX_SRC_RDY_N => TX_SRC_RDY_N,
                    TX_SOF_N => TX_SOF_N,
                    TX_EOF_N => TX_EOF_N,
                    TX_REM => TX_REM,
                    TX_DST_RDY_N => tx_dst_rdy_n_i,

        -- UFC Interface

                    UFC_TX_REQ_N => UFC_TX_REQ_N,
                    UFC_TX_MS => UFC_TX_MS,
                    UFC_TX_ACK_N => UFC_TX_ACK_N_Buffer,

        -- Clock Compensation Interface

                    WARN_CC => WARN_CC,
                    DO_CC => DO_CC,

        -- Global Logic Interface

                    CHANNEL_UP => CHANNEL_UP,

        -- TX_LL Control Module Interface

                    HALT_C => halt_c_i,
                    UFC_MESSAGE => ufc_message_i,

        -- Aurora Lane Interface

                    GEN_SCP => GEN_SCP_Buffer,
                    GEN_ECP => GEN_ECP_Buffer,
                    GEN_SUF => GEN_SUF_Buffer,
                    FC_NB => FC_NB_Buffer,
                    GEN_CC => GEN_CC_Buffer,

        -- System Interface

                    USER_CLK => USER_CLK

                 );

end MAPPED;
