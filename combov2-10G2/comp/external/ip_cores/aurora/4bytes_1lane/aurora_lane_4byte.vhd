--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: aurora_lane_4byte.vhd,v $
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
--  AURORA_LANE_4BYTE
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: the AURORA_LANE_4BYTE module provides a full duplex 4-byte aurora lane
--               connection using a single MGT.  The module handles lane initialization,
--               symbol generation and decoding and error detection.  It also decodes
--               some of the channel bonding indicator signals needed by the Global
--               logic.
--
--               * Supports Virtex 2 Pro
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_4byte1lane;

entity AURORA_LANE_4BYTE is
    generic (                    
            EXTEND_WATCHDOGS   : boolean := FALSE
    );
    port (

    -- MGT Interface

            RX_DATA           : in std_logic_vector(31 downto 0);  -- 4-byte data bus from the MGT.
            RX_NOT_IN_TABLE   : in std_logic_vector(3 downto 0);   -- Invalid 10-bit code was recieved.
            RX_DISP_ERR       : in std_logic_vector(3 downto 0);   -- Disparity error detected on RX interface.
            RX_CHAR_IS_K      : in std_logic_vector(3 downto 0);   -- Indicates which bytes of RX_DATA are control.
            RX_CHAR_IS_COMMA  : in std_logic_vector(3 downto 0);   -- Comma received on given byte.
            RX_BUF_STATUS     : in std_logic;                      -- Overflow/Underflow of RX buffer detected.
            TX_BUF_ERR        : in std_logic;                      -- Overflow/Underflow of TX buffer detected.
            TX_K_ERR          : in std_logic_vector(3 downto 0);   -- Attempt to send bad control byte detected.
            RX_CLK_COR_CNT    : in std_logic_vector(2 downto 0);   -- Value used to determine channel bonding status.
            RX_REALIGN        : in std_logic;                      -- SERDES was realigned because of a new comma.
            RX_POLARITY       : out std_logic;                     -- Controls interpreted polarity of serial data inputs.
            RX_RESET          : out std_logic;                     -- Reset RX side of MGT logic.
            TX_CHAR_IS_K      : out std_logic_vector(3 downto 0);  -- TX_DATA byte is a control character.
            TX_DATA           : out std_logic_vector(31 downto 0); -- 4-byte data bus to the MGT.
            TX_RESET          : out std_logic;                     -- Reset TX side of MGT logic.

    -- Comma Detect Phase Align Interface

            ENA_COMMA_ALIGN   : out std_logic;                     -- Request comma alignment.

    -- TX_LL Interface

            GEN_SCP           : in std_logic_vector(0 to 1);       -- SCP generation request from TX_LL.
            GEN_ECP           : in std_logic_vector(0 to 1);       -- ECP generation request from TX_LL.
            GEN_SNF           : in std_logic_vector(0 to 1);       -- SNF generation request from TX_LL.
            GEN_SUF           : in std_logic_vector(0 to 1);       -- SUF generation request from TX_LL.
            GEN_PAD           : in std_logic_vector(0 to 1);       -- PAD generation request from TX_LL.
            FC_NB             : in std_logic_vector(0 to 7);       -- Size code for SUF and SNF messages.
            TX_PE_DATA        : in std_logic_vector(0 to 31);      -- Data from TX_LL to send over lane.
            TX_PE_DATA_V      : in std_logic_vector(0 to 1);       -- Indicates TX_PE_DATA is Valid.
            GEN_CC            : in std_logic;                      -- CC generation request from TX_LL.

    -- RX_LL Interface

            RX_PAD            : out std_logic_vector(0 to 1);      -- Indicates lane received PAD.
            RX_PE_DATA        : out std_logic_vector(0 to 31);     -- RX data from lane to RX_LL.
            RX_PE_DATA_V      : out std_logic_vector(0 to 1);      -- RX_PE_DATA is data, not control symbol.
            RX_SCP            : out std_logic_vector(0 to 1);      -- Indicates lane received SCP.
            RX_ECP            : out std_logic_vector(0 to 1);      -- Indicates lane received ECP.
            RX_SNF            : out std_logic_vector(0 to 1);      -- Indicates lane received SNF.
            RX_SUF            : out std_logic_vector(0 to 1);      -- Indicates lane received SUF.
            RX_FC_NB          : out std_logic_vector(0 to 7);      -- Size code for SNF or SUF.

    -- Global Logic Interface

            GEN_A             : in std_logic;                      -- 'A character' generation request from Global Logic.
            GEN_K             : in std_logic_vector(0 to 3);       -- 'K character' generation request from Global Logic.
            GEN_R             : in std_logic_vector(0 to 3);       -- 'R character' generation request from Global Logic.
            GEN_V             : in std_logic_vector(0 to 3);       -- Verification data generation request.
            LANE_UP           : out std_logic;                     -- Lane is ready for bonding and verification.
            SOFT_ERROR        : out std_logic_vector(0 to 1);      -- Soft error detected.
            HARD_ERROR        : out std_logic;                     -- Hard error detected.
            CHANNEL_BOND_LOAD : out std_logic;                     -- Channel Bongding done code recieved.
            GOT_A             : out std_logic_vector(0 to 3);      -- Indicates lane recieved 'A character' bytes.
            GOT_V             : out std_logic;                     -- Verification symbols received.

    -- System Interface

            USER_CLK          : in std_logic;                      -- System clock for all non-MGT Aurora Logic.
            RESET             : in std_logic                       -- Reset the lane.

         );

end AURORA_LANE_4BYTE;

architecture MAPPED of AURORA_LANE_4BYTE is

-- External Register Declarations --

    signal RX_POLARITY_Buffer       : std_logic;
    signal RX_RESET_Buffer          : std_logic;
    signal TX_CHAR_IS_K_Buffer      : std_logic_vector(3 downto 0);
    signal TX_DATA_Buffer           : std_logic_vector(31 downto 0);
    signal TX_RESET_Buffer          : std_logic;
    signal ENA_COMMA_ALIGN_Buffer   : std_logic;
    signal RX_PAD_Buffer            : std_logic_vector(0 to 1);
    signal RX_PE_DATA_Buffer        : std_logic_vector(0 to 31);
    signal RX_PE_DATA_V_Buffer      : std_logic_vector(0 to 1);
    signal RX_SCP_Buffer            : std_logic_vector(0 to 1);
    signal RX_ECP_Buffer            : std_logic_vector(0 to 1);
    signal RX_SNF_Buffer            : std_logic_vector(0 to 1);
    signal RX_SUF_Buffer            : std_logic_vector(0 to 1);
    signal RX_FC_NB_Buffer          : std_logic_vector(0 to 7);
    signal LANE_UP_Buffer           : std_logic;
    signal SOFT_ERROR_Buffer        : std_logic_vector(0 to 1);
    signal HARD_ERROR_Buffer        : std_logic;
    signal CHANNEL_BOND_LOAD_Buffer : std_logic;
    signal GOT_A_Buffer             : std_logic_vector(0 to 3);
    signal GOT_V_Buffer             : std_logic;

-- Wire Declarations --

    signal ena_comma_align_i     : std_logic;
    signal gen_sp_i              : std_logic;
    signal gen_spa_i             : std_logic;
    signal rx_sp_i               : std_logic;
    signal rx_spa_i              : std_logic;
    signal rx_neg_i              : std_logic;
    signal enable_error_detect_i : std_logic;
    signal do_word_align_i       : std_logic;
    signal hard_error_reset_i    : std_logic;

-- Component Declarations --

    component LANE_INIT_SM_4BYTE
        generic (                    
                EXTEND_WATCHDOGS   : boolean := FALSE
        );
        port (

        -- MGT Interface

                RX_NOT_IN_TABLE     : in std_logic_vector(3 downto 0); -- MGT received invalid 10b code
                RX_DISP_ERR         : in std_logic_vector(3 downto 0); -- MGT received 10b code w/ wrong disparity
                RX_CHAR_IS_COMMA    : in std_logic_vector(3 downto 0); -- MGT received a Comma
                RX_REALIGN          : in std_logic;                    -- MGT had to change alignment due to new comma
                RX_RESET            : out std_logic;                   -- Reset the RX side of the MGT
                TX_RESET            : out std_logic;                   -- Reset the TX side of the MGT
                RX_POLARITY         : out std_logic;                   -- Sets polarity used to interpet rx'ed symbols

        -- Comma Detect Phase Alignment Interface

                ENA_COMMA_ALIGN     : out std_logic;                   -- Turn on SERDES Alignment in MGT

        -- Symbol Generator Interface

                GEN_SP              : out std_logic;                   -- Generate SP symbol
                GEN_SPA             : out std_logic;                   -- Generate SPA symbol

        -- Symbol Decoder Interface

                RX_SP               : in std_logic;                    -- Lane rx'ed SP sequence w/ + or - data
                RX_SPA              : in std_logic;                    -- Lane rx'ed SPA sequence
                RX_NEG              : in std_logic;                    -- Lane rx'ed inverted SP or SPA data
                DO_WORD_ALIGN       : out std_logic;                   -- Enable word alignment

        -- Error Detection Logic Interface

                ENABLE_ERROR_DETECT : out std_logic;                   -- Turn on Soft Error detection
                HARD_ERROR_RESET    : in std_logic;                    -- Reset lane due to hard error

        -- Global Logic Interface

                LANE_UP             : out std_logic;                   -- Lane is initialized

        -- System Interface

                USER_CLK            : in std_logic;                    -- Clock for all non-MGT Aurora logic
                RESET               : in std_logic                     -- Reset Aurora Lane

             );

    end component;


    component CHBOND_COUNT_DEC_4BYTE

        port (

                RX_CLK_COR_CNT    : in std_logic_vector(2 downto 0);
                CHANNEL_BOND_LOAD : out std_logic;
                USER_CLK          : in std_logic

             );

    end component;


    component SYM_GEN_4BYTE

        port (

        -- TX_LL Interface                                        -- See description for info about GEN_PAD and TX_PE_DATA_V.

                GEN_SCP      : in std_logic_vector(0 to 1);       -- Generate SCP.
                GEN_ECP      : in std_logic_vector(0 to 1);       -- Generate ECP.
                GEN_SNF      : in std_logic_vector(0 to 1);       -- Generate SNF using code given by FC_NB.
                GEN_SUF      : in std_logic_vector(0 to 1);       -- Generate SUF using code given by FC_NB.
                GEN_PAD      : in std_logic_vector(0 to 1);       -- Replace LSB with Pad character.
                FC_NB        : in std_logic_vector(0 to 7);       -- Size code for Flow Control messages.
                TX_PE_DATA   : in std_logic_vector(0 to 31);      -- Data.  Transmitted when TX_PE_DATA_V is asserted.
                TX_PE_DATA_V : in std_logic_vector(0 to 1);       -- Transmit data.
                GEN_CC       : in std_logic;                      -- Generate Clock Correction symbols.

        -- Global Logic Interface                                 -- See description for info about GEN_K,GEN_R and GEN_A.

                GEN_A        : in std_logic;                      -- Generate A character for MSBYTE
                GEN_K        : in std_logic_vector(0 to 3);       -- Generate K character for selected bytes.
                GEN_R        : in std_logic_vector(0 to 3);       -- Generate R character for selected bytes.
                GEN_V        : in std_logic_vector(0 to 3);       -- Generate Ver data character on selected bytes.

        -- Lane Init SM Interface

                GEN_SP       : in std_logic;                      -- Generate SP pattern.
                GEN_SPA      : in std_logic;                      -- Generate SPA pattern.

        -- MGT Interface

                TX_CHAR_IS_K : out std_logic_vector(3 downto 0);  -- Transmit TX_DATA as a control character.
                TX_DATA      : out std_logic_vector(31 downto 0); -- Data to MGT for transmission to channel partner.

        -- System Interface

                USER_CLK     : in std_logic                       -- Clock for all non-MGT Aurora Logic.

             );

    end component;


    component SYM_DEC_4BYTE

        port (

        -- RX_LL Interface

                RX_PAD           : out std_logic_vector(0 to 1);     -- LSByte is PAD.
                RX_PE_DATA       : out std_logic_vector(0 to 31);    -- Word aligned data from channel partner.
                RX_PE_DATA_V     : out std_logic_vector(0 to 1);     -- Data is valid data and not a control character.
                RX_SCP           : out std_logic_vector(0 to 1);     -- SCP symbol received.
                RX_ECP           : out std_logic_vector(0 to 1);     -- ECP symbol received.
                RX_SNF           : out std_logic_vector(0 to 1);     -- SNF symbol received.
                RX_SUF           : out std_logic_vector(0 to 1);     -- SUF symbol reveived.
                RX_FC_NB         : out std_logic_vector(0 to 7);     -- Flow Control size code.  Valid with RX_SNF or RX_SUF.

        -- Lane Init SM Interface

                DO_WORD_ALIGN    : in std_logic;                     -- Word alignment is allowed.
                LANE_UP          : in std_logic;
                RX_SP            : out std_logic;                    -- SP sequence received with positive or negative data.
                RX_SPA           : out std_logic;                    -- SPA sequence received.
                RX_NEG           : out std_logic;                    -- Inverted data for SP or SPA received.

        -- Global Logic Interface

                GOT_A            : out std_logic_vector(0 to 3);     -- A character received on indicated byte(s).
                GOT_V            : out std_logic;                    -- V sequence received.

        -- MGT Interface

                RX_DATA          : in std_logic_vector(31 downto 0); -- Raw RX data from MGT.
                RX_CHAR_IS_K     : in std_logic_vector(3 downto 0);  -- Bits indicating which bytes are control characters.
                RX_CHAR_IS_COMMA : in std_logic_vector(3 downto 0);  -- Rx'ed a comma.

        -- System Interface

                USER_CLK         : in std_logic;                     -- System clock for all non-MGT Aurora Logic.
                RESET            : in std_logic

             );

    end component;


    component ERROR_DETECT_4BYTE

        port (

        -- Lane Init SM Interface

                ENABLE_ERROR_DETECT : in std_logic;
                HARD_ERROR_RESET    : out std_logic;

        -- Global Logic Interface

                SOFT_ERROR          : out std_logic_vector(0 to 1);
                HARD_ERROR          : out std_logic;

        -- MGT Interface

                RX_DISP_ERR         : in std_logic_vector(3 downto 0);
                TX_K_ERR            : in std_logic_vector(3 downto 0);
                RX_NOT_IN_TABLE     : in std_logic_vector(3 downto 0);
                RX_BUF_STATUS       : in std_logic;
                TX_BUF_ERR          : in std_logic;
                RX_REALIGN          : in std_logic;

        -- System Interface

                USER_CLK            : in std_logic

             );

    end component;

begin

    RX_POLARITY       <= RX_POLARITY_Buffer;
    RX_RESET          <= RX_RESET_Buffer;
    TX_CHAR_IS_K      <= TX_CHAR_IS_K_Buffer;
    TX_DATA           <= TX_DATA_Buffer;
    TX_RESET          <= TX_RESET_Buffer;
    ENA_COMMA_ALIGN   <= ENA_COMMA_ALIGN_Buffer;
    RX_PAD            <= RX_PAD_Buffer;
    RX_PE_DATA        <= RX_PE_DATA_Buffer;
    RX_PE_DATA_V      <= RX_PE_DATA_V_Buffer;
    RX_SCP            <= RX_SCP_Buffer;
    RX_ECP            <= RX_ECP_Buffer;
    RX_SNF            <= RX_SNF_Buffer;
    RX_SUF            <= RX_SUF_Buffer;
    RX_FC_NB          <= RX_FC_NB_Buffer;
    LANE_UP           <= LANE_UP_Buffer;
    SOFT_ERROR        <= SOFT_ERROR_Buffer;
    HARD_ERROR        <= HARD_ERROR_Buffer;
    CHANNEL_BOND_LOAD <= CHANNEL_BOND_LOAD_Buffer;
    GOT_A             <= GOT_A_Buffer;
    GOT_V             <= GOT_V_Buffer;

-- Main Body of Code --

    -- Lane Initialization state machine

    lane_init_sm_4byte_i : LANE_INIT_SM_4BYTE
        generic map (                    
                EXTEND_WATCHDOGS        => EXTEND_WATCHDOGS
        )
        port map (

        -- MGT Interface

                    RX_NOT_IN_TABLE     => RX_NOT_IN_TABLE,
                    RX_DISP_ERR         => RX_DISP_ERR,
                    RX_CHAR_IS_COMMA    => RX_CHAR_IS_COMMA,
                    RX_REALIGN          => RX_REALIGN,
                    RX_RESET            => RX_RESET_Buffer,
                    TX_RESET            => TX_RESET_Buffer,
                    RX_POLARITY         => RX_POLARITY_Buffer,

        -- Comma Detect Phase Alignment Interface

                    ENA_COMMA_ALIGN     => ENA_COMMA_ALIGN_Buffer,

        -- Symbol Generator Interface

                    GEN_SP              => gen_sp_i,
                    GEN_SPA             => gen_spa_i,

        -- Symbol Decoder Interface

                    RX_SP               => rx_sp_i,
                    RX_SPA              => rx_spa_i,
                    RX_NEG              => rx_neg_i,
                    DO_WORD_ALIGN       => do_word_align_i,

        -- Error Detection Logic Interface

                    HARD_ERROR_RESET    => hard_error_reset_i,
                    ENABLE_ERROR_DETECT => enable_error_detect_i,

        -- Global Logic Interface

                    LANE_UP             => LANE_UP_Buffer,

        -- System Interface

                    USER_CLK            => USER_CLK,
                    RESET               => RESET

                 );



    -- Channel Bonding Count Decode module

    chbond_count_dec_4byte_i : CHBOND_COUNT_DEC_4BYTE

        port map (

                    RX_CLK_COR_CNT    => RX_CLK_COR_CNT,
                    CHANNEL_BOND_LOAD => CHANNEL_BOND_LOAD_Buffer,
                    USER_CLK          => USER_CLK

                 );


    -- Symbol Generation module

    sym_gen_4byte_i : SYM_GEN_4BYTE

        port map (

        -- TX_LL Interface

                    GEN_SCP      => GEN_SCP,
                    GEN_ECP      => GEN_ECP,
                    GEN_SNF      => GEN_SNF,
                    GEN_SUF      => GEN_SUF,
                    GEN_PAD      => GEN_PAD,
                    FC_NB        => FC_NB,
                    TX_PE_DATA   => TX_PE_DATA,
                    TX_PE_DATA_V => TX_PE_DATA_V,
                    GEN_CC       => GEN_CC,

        -- Global Logic Interface

                    GEN_A        => GEN_A,
                    GEN_K        => GEN_K,
                    GEN_R        => GEN_R,
                    GEN_V        => GEN_V,

        -- Lane Init SM Interface

                    GEN_SP       => gen_sp_i,
                    GEN_SPA      => gen_spa_i,

        -- MGT Interface

                    TX_CHAR_IS_K => TX_CHAR_IS_K_Buffer,
                    TX_DATA      => TX_DATA_Buffer,

        -- System Interface

                    USER_CLK     => USER_CLK

                 );


    -- Symbol Decode module

    sym_dec_4byte_i : SYM_DEC_4BYTE

        port map (

        -- RX_LL Interface

                    RX_PAD           => RX_PAD_Buffer,
                    RX_PE_DATA       => RX_PE_DATA_Buffer,
                    RX_PE_DATA_V     => RX_PE_DATA_V_Buffer,
                    RX_SCP           => RX_SCP_Buffer,
                    RX_ECP           => RX_ECP_Buffer,
                    RX_SNF           => RX_SNF_Buffer,
                    RX_SUF           => RX_SUF_Buffer,
                    RX_FC_NB         => RX_FC_NB_Buffer,

        -- Lane Init SM Interface

                    DO_WORD_ALIGN    => do_word_align_i,
                    LANE_UP          => LANE_UP_Buffer,
                    RX_SP            => rx_sp_i,
                    RX_SPA           => rx_spa_i,
                    RX_NEG           => rx_neg_i,

        -- Global Logic Interface

                    GOT_A            => GOT_A_Buffer,
                    GOT_V            => GOT_V_Buffer,

        -- MGT Interface

                    RX_DATA          => RX_DATA,
                    RX_CHAR_IS_K     => RX_CHAR_IS_K,
                    RX_CHAR_IS_COMMA => RX_CHAR_IS_COMMA,

        -- System Interface

                    USER_CLK         => USER_CLK,
                    RESET            => RESET

                 );


    -- Error Detection module

    error_detect_4byte_i : ERROR_DETECT_4BYTE

        port map (

        -- Lane Init SM Interface

                    ENABLE_ERROR_DETECT => enable_error_detect_i,
                    HARD_ERROR_RESET    => hard_error_reset_i,

        -- Global Logic Interface

                    SOFT_ERROR          => SOFT_ERROR_Buffer,
                    HARD_ERROR          => HARD_ERROR_Buffer,

        -- MGT Interface

                    RX_DISP_ERR         => RX_DISP_ERR,
                    TX_K_ERR            => TX_K_ERR,
                    RX_NOT_IN_TABLE     => RX_NOT_IN_TABLE,
                    RX_BUF_STATUS       => RX_BUF_STATUS,
                    TX_BUF_ERR          => TX_BUF_ERR,
                    RX_REALIGN          => RX_REALIGN,

        -- System Interface

                    USER_CLK            => USER_CLK

                 );

end MAPPED;
