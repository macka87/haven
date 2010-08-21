--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: rx_ll.vhd,v $
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
--  RX_LL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: The RX_LL module receives data from the Aurora Channel,
--               converts it to LocalLink and sends it to the user interface.
--               It also handles NFC and UFC messages.
--
--               This module supports 2 4-byte lane designs.
--
--               This module supports Immediate Mode Native Flow Control.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity RX_LL is

    port (

    -- LocalLink PDU Interface

            RX_D             : out std_logic_vector(0 to 31);
            RX_REM           : out std_logic_vector(0 to 1);
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Global Logic Interface

            START_RX         : in std_logic;

    -- Aurora Lane Interface

            RX_PAD           : in std_logic_vector(0 to 1);
            RX_PE_DATA       : in std_logic_vector(0 to 31);
            RX_PE_DATA_V     : in std_logic_vector(0 to 1);
            RX_SCP           : in std_logic_vector(0 to 1);
            RX_ECP           : in std_logic_vector(0 to 1);
            RX_SNF           : in std_logic_vector(0 to 1);
            RX_FC_NB         : in std_logic_vector(0 to 7);

    -- TX_LL Interface

            DECREMENT_NFC    : in std_logic;
            TX_WAIT          : out std_logic;

    -- Error Interface

            FRAME_ERROR      : out std_logic;

    -- System Interface

            USER_CLK         : in std_logic

         );

end RX_LL;

architecture MAPPED of RX_LL is

-- External Register Declarations --

    signal RX_D_Buffer             : std_logic_vector(0 to 31);
    signal RX_REM_Buffer           : std_logic_vector(0 to 1);
    signal RX_SRC_RDY_N_Buffer     : std_logic;
    signal RX_SOF_N_Buffer         : std_logic;
    signal RX_EOF_N_Buffer         : std_logic;
    signal TX_WAIT_Buffer          : std_logic;
    signal FRAME_ERROR_Buffer      : std_logic;

-- Wire Declarations --

    signal start_rx_i          : std_logic;

-- Component Declarations --

    component RX_LL_NFC

        port (

        -- Aurora Lane Interface

                RX_SNF        : in  std_logic_vector(0 to 1);
                RX_FC_NB      : in  std_logic_vector(0 to 7);

        -- TX_LL Interface

                DECREMENT_NFC : in  std_logic;
                TX_WAIT       : out std_logic;

        -- Global Logic Interface

                CHANNEL_UP    : in  std_logic;

        -- USER Interface

                USER_CLK      : in  std_logic

             );

    end component;


    component RX_LL_PDU_DATAPATH

        port (

        -- Traffic Separator Interface

                PDU_DATA     : in std_logic_vector(0 to 31);
                PDU_DATA_V   : in std_logic_vector(0 to 1);
                PDU_PAD      : in std_logic_vector(0 to 1);
                PDU_SCP      : in std_logic_vector(0 to 1);
                PDU_ECP      : in std_logic_vector(0 to 1);

        -- LocalLink PDU Interface

                RX_D         : out std_logic_vector(0 to 31);
                RX_REM       : out std_logic_vector(0 to 1);
                RX_SRC_RDY_N : out std_logic;
                RX_SOF_N     : out std_logic;
                RX_EOF_N     : out std_logic;

        -- Error Interface

                FRAME_ERROR  : out std_logic;

        -- System Interface

                USER_CLK     : in std_logic;
                RESET        : in std_logic

             );

    end component;


begin

    RX_D             <= RX_D_Buffer;
    RX_REM           <= RX_REM_Buffer;
    RX_SRC_RDY_N     <= RX_SRC_RDY_N_Buffer;
    RX_SOF_N         <= RX_SOF_N_Buffer;
    RX_EOF_N         <= RX_EOF_N_Buffer;
    TX_WAIT          <= TX_WAIT_Buffer;
    FRAME_ERROR      <= FRAME_ERROR_Buffer;

    start_rx_i       <= not START_RX;

-- Main Body of Code --

    -- NFC processing --

    nfc_module_i : RX_LL_NFC

        port map (

        -- Aurora Lane Interface

                    RX_SNF        => RX_SNF,
                    RX_FC_NB      => RX_FC_NB,

        -- TX_LL Interface

                    DECREMENT_NFC => DECREMENT_NFC,
                    TX_WAIT       => TX_WAIT_Buffer,

        -- Global Logic Interface

                    CHANNEL_UP    => START_RX,

        -- USER Interface

                    USER_CLK      => USER_CLK

                 );


    -- Datapath for user PDUs --

    rx_ll_pdu_datapath_i : RX_LL_PDU_DATAPATH

        port map (

        -- Traffic Separator Interface

                    PDU_DATA     => RX_PE_DATA,
                    PDU_DATA_V   => RX_PE_DATA_V,
                    PDU_PAD      => RX_PAD,
                    PDU_SCP      => RX_SCP,
                    PDU_ECP      => RX_ECP,

        -- LocalLink PDU Interface

                    RX_D         => RX_D_Buffer,
                    RX_REM       => RX_REM_Buffer,
                    RX_SRC_RDY_N => RX_SRC_RDY_N_Buffer,
                    RX_SOF_N     => RX_SOF_N_Buffer,
                    RX_EOF_N     => RX_EOF_N_Buffer,

        -- Error Interface

                    FRAME_ERROR  => FRAME_ERROR_Buffer,

        -- System Interface

                    USER_CLK     => USER_CLK,
                    RESET        => start_rx_i

                 );


end MAPPED;
