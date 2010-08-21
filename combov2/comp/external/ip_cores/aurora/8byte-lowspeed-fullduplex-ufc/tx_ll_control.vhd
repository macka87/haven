--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: tx_ll_control.vhd,v $
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
--  TX_LL_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: This module provides the transmitter state machine
--               control logic to connect the LocalLink interface to
--               the Aurora Channel.
--
--               This module supports 4 4-byte lane designs
--
--               This module supports User Flow Control.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use WORK.AURORA.all;

-- synthesis translate_off
library UNISIM;
use UNISIM.all;
-- synthesis translate_on

entity TX_LL_CONTROL is

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

end TX_LL_CONTROL;

architecture RTL of TX_LL_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal TX_DST_RDY_N_Buffer  : std_logic;
    signal UFC_TX_ACK_N_Buffer  : std_logic;
    signal HALT_C_Buffer        : std_logic;
    signal UFC_MESSAGE_Buffer   : std_logic_vector(0 to 3);
    signal GEN_SCP_Buffer       : std_logic;
    signal GEN_ECP_Buffer       : std_logic;
    signal GEN_SUF_Buffer       : std_logic;
    signal FC_NB_Buffer         : std_logic_vector(0 to 3);
    signal GEN_CC_Buffer        : std_logic_vector(0 to 1);

-- Internal Register Declarations --

    signal do_cc_r                      : std_logic;
    signal warn_cc_r                    : std_logic;
    signal ufc_idle_r                   : std_logic;
    signal ufc_header_r                 : std_logic;
    signal ufc_message1_r               : std_logic;
    signal ufc_message2_r               : std_logic;
    signal ufc_message3_r               : std_logic;
    signal ufc_message4_r               : std_logic;
    signal ufc_message5_r               : std_logic;
    signal ufc_message6_r               : std_logic;
    signal ufc_message7_r               : std_logic;
    signal ufc_message8_r               : std_logic;

    signal ufc_message_count_r          : std_logic_vector(0 to 2);

    signal suf_delay_1_r                : std_logic;
    signal suf_delay_2_r                : std_logic;

    signal delay_ms_1_r                 : std_logic_vector(0 to 3);
    signal delay_ms_2_r                 : std_logic_vector(0 to 3);

    signal previous_cycle_ufc_message_r : std_logic;
    signal create_gap_for_scp_r         : std_logic;

    signal idle_r                       : std_logic;
    signal sof_to_data_r                : std_logic;
    signal data_r                       : std_logic;
    signal data_to_eof_1_r              : std_logic;
    signal data_to_eof_2_r              : std_logic;
    signal eof_r                        : std_logic;
    signal sof_to_eof_1_r               : std_logic;
    signal sof_to_eof_2_r               : std_logic;
    signal sof_and_eof_r                : std_logic;

    signal gen_scp_pipeline_r           : std_logic;
    signal gen_ecp_pipeline_r           : std_logic;
    signal gen_suf_pipeline_r           : std_logic;
    signal fc_nb_pipeline_r             : std_logic_vector(0 to 3);
    signal gen_cc_pipeline_r            : std_logic;

-- Wire Declarations --

    signal next_ufc_idle_c       : std_logic;
    signal next_ufc_header_c     : std_logic;
    signal next_ufc_message1_c   : std_logic;
    signal next_ufc_message2_c   : std_logic;
    signal next_ufc_message3_c   : std_logic;
    signal next_ufc_message4_c   : std_logic;
    signal next_ufc_message5_c   : std_logic;
    signal next_ufc_message6_c   : std_logic;
    signal next_ufc_message7_c   : std_logic;
    signal next_ufc_message8_c   : std_logic;
    signal ufc_ok_c : std_logic;
    signal create_gap_for_scp_c  : std_logic;

    signal next_idle_c           : std_logic;
    signal next_sof_to_data_c    : std_logic;
    signal next_data_c           : std_logic;
    signal next_data_to_eof_1_c  : std_logic;
    signal next_data_to_eof_2_c  : std_logic;
    signal next_eof_c            : std_logic;
    signal next_sof_to_eof_1_c   : std_logic;
    signal next_sof_to_eof_2_c   : std_logic;
    signal next_sof_and_eof_c    : std_logic;

    signal fc_nb_c               : std_logic_vector(0 to 3);
    signal tx_dst_rdy_n_c        : std_logic;
    signal do_sof_c              : std_logic;
    signal do_eof_c              : std_logic;
    signal channel_full_c        : std_logic;
    signal pdu_ok_c              : std_logic;

-- Declarations to handle VHDL limitations
    signal reset_i               : std_logic;

-- Component Declarations --

    component FDR

        generic (INIT : bit := '0');

        port (

                Q : out std_ulogic;
                C : in  std_ulogic;
                D : in  std_ulogic;
                R : in  std_ulogic

             );

    end component;

begin

    TX_DST_RDY_N  <= TX_DST_RDY_N_Buffer;
    UFC_TX_ACK_N  <= UFC_TX_ACK_N_Buffer;
    HALT_C        <= HALT_C_Buffer;
    UFC_MESSAGE   <= UFC_MESSAGE_Buffer;
    GEN_SCP       <= GEN_SCP_Buffer;
    GEN_ECP       <= GEN_ECP_Buffer;
    GEN_SUF       <= GEN_SUF_Buffer;
    FC_NB         <= FC_NB_Buffer;
    GEN_CC        <= GEN_CC_Buffer;

-- Main Body of Code --



    reset_i <=  not CHANNEL_UP;


    -- Clock Compensation --

    -- Register the DO_CC and WARN_CC signals for internal use.  Note that the raw DO_CC
    -- signal is used for some logic so the DO_CC signal should be driven directly
    -- from a register whenever possible.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                do_cc_r <= '0' after DLY;

            else

                do_cc_r <= DO_CC after DLY;

            end if;

        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                warn_cc_r <= '0' after DLY;

            else

                warn_cc_r <= WARN_CC after DLY;

            end if;

        end if;

    end process;




    -- UFC State Machine --

    -- The UFC state machine has 10 states: waiting for a UFC request, sending
    -- a UFC header, and 8 states for sending up to 8 words of a UFC message.
    -- It can take over the channel at any time except when there is an NFC
    -- message or a CC sequence being sent.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                ufc_idle_r     <= '1' after DLY;
                ufc_header_r   <= '0' after DLY;
                ufc_message1_r <= '0' after DLY;
                ufc_message2_r <= '0' after DLY;
                ufc_message3_r <= '0' after DLY;
                ufc_message4_r <= '0' after DLY;
                ufc_message5_r <= '0' after DLY;
                ufc_message6_r <= '0' after DLY;
                ufc_message7_r <= '0' after DLY;
                ufc_message8_r <= '0' after DLY;

            else

                ufc_idle_r     <= next_ufc_idle_c     after DLY;
                ufc_header_r   <= next_ufc_header_c   after DLY;
                ufc_message1_r <= next_ufc_message1_c after DLY;
                ufc_message2_r <= next_ufc_message2_c after DLY;
                ufc_message3_r <= next_ufc_message3_c after DLY;
                ufc_message4_r <= next_ufc_message4_c after DLY;
                ufc_message5_r <= next_ufc_message5_c after DLY;
                ufc_message6_r <= next_ufc_message6_c after DLY;
                ufc_message7_r <= next_ufc_message7_c after DLY;
                ufc_message8_r <= next_ufc_message8_c after DLY;

            end if;

        end if;

    end process;


    -- Capture the message count so it can be used to determine the appropriate
    -- next state.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (next_ufc_header_c = '1') then

                ufc_message_count_r <= UFC_TX_MS(0 to 2) after DLY;

            end if;

        end if;

    end process;



    next_ufc_idle_c     <= ((UFC_TX_REQ_N or not ufc_ok_c) and
                           ((ufc_idle_r) or
                           (ufc_message1_r) or
                           (ufc_message2_r) or
                           (ufc_message3_r) or
                           (ufc_message4_r and std_bool(ufc_message_count_r = "011")) or
                           (ufc_message5_r) or
                           (ufc_message6_r) or
                           (ufc_message7_r) or
                           (ufc_message8_r)));


    next_ufc_header_c   <= ((not UFC_TX_REQ_N and ufc_ok_c) and
                           ((ufc_idle_r) or
                           (ufc_message1_r) or
                           (ufc_message2_r) or
                           (ufc_message3_r) or
                           (ufc_message4_r and std_bool(ufc_message_count_r = "011")) or
                           (ufc_message5_r) or
                           (ufc_message6_r) or
                           (ufc_message7_r) or
                           (ufc_message8_r)));


    next_ufc_message1_c <= ufc_header_r   and std_bool(ufc_message_count_r = "000");

    next_ufc_message2_c <= ufc_header_r   and std_bool(ufc_message_count_r = "001");

    next_ufc_message3_c <= ufc_header_r   and std_bool(ufc_message_count_r = "010");

    next_ufc_message4_c <= ufc_header_r   and std_bool(ufc_message_count_r > "010");

    next_ufc_message5_c <= ufc_message4_r and std_bool(ufc_message_count_r = "100");

    next_ufc_message6_c <= ufc_message4_r and std_bool(ufc_message_count_r = "101");

    next_ufc_message7_c <= ufc_message4_r and std_bool(ufc_message_count_r = "110");

    next_ufc_message8_c <= ufc_message4_r and std_bool(ufc_message_count_r = "111");


    UFC_MESSAGE_Buffer(0)      <= not ufc_idle_r and
                                  not ufc_header_r;

    UFC_MESSAGE_Buffer(1)      <= ((not ufc_idle_r      and
                                    not ufc_header_r)   and
                                    not ufc_message1_r) and
                                    not ufc_message5_r;

    UFC_MESSAGE_Buffer(2)      <= ufc_message3_r or
                                  ufc_message4_r or
                                  ufc_message7_r or
                                  ufc_message8_r;

    UFC_MESSAGE_Buffer(3)      <= ufc_message4_r or
                                  ufc_message8_r;


    ufc_ok_c <= not do_cc_r and not warn_cc_r;


    UFC_TX_ACK_N_Buffer <= not ufc_header_r;


    -- Delay UFC_TX_MS so it arrives at the lanes at the same time as the
    -- UFC header.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            delay_ms_1_r <= UFC_TX_MS    after DLY;
            delay_ms_2_r <= delay_ms_1_r after DLY;

        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            previous_cycle_ufc_message_r <= not ufc_idle_r and not ufc_header_r after DLY;

        end if;

    end process;


    -- PDU State Machine --

    -- The PDU state machine handles the encapsulation and transmission of user
    -- PDUs.  It can use the channel when there is no CC, NFC message, UFC header,
    -- UFC message or remote NFC request.

    -- State Registers

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                idle_r          <= '1' after DLY;
                sof_to_data_r   <= '0' after DLY;
                data_r          <= '0' after DLY;
                data_to_eof_1_r <= '0' after DLY;
                data_to_eof_2_r <= '0' after DLY;
                eof_r           <= '0' after DLY;
                sof_to_eof_1_r  <= '0' after DLY;
                sof_to_eof_2_r  <= '0' after DLY;
                sof_and_eof_r   <= '0' after DLY;

            else

                if (pdu_ok_c = '1') then

                    idle_r          <= next_idle_c          after DLY;
                    sof_to_data_r   <= next_sof_to_data_c   after DLY;
                    data_r          <= next_data_c          after DLY;
                    data_to_eof_1_r <= next_data_to_eof_1_c after DLY;
                    data_to_eof_2_r <= next_data_to_eof_2_c after DLY;
                    eof_r           <= next_eof_c           after DLY;
                    sof_to_eof_1_r  <= next_sof_to_eof_1_c  after DLY;
                    sof_to_eof_2_r  <= next_sof_to_eof_2_c  after DLY;
                    sof_and_eof_r   <= next_sof_and_eof_c   after DLY;

                end if;

            end if;

        end if;

    end process;


    -- Next State Logic

    next_idle_c          <= (idle_r and not do_sof_c)          or
                            (data_to_eof_2_r and not do_sof_c) or
                            (eof_r and not do_sof_c )          or
                            (sof_to_eof_2_r and not do_sof_c)  or
                            (sof_and_eof_r and not do_sof_c);


    next_sof_to_data_c   <= ((idle_r and do_sof_c) and not do_eof_c)          or
                            ((data_to_eof_2_r and do_sof_c) and not do_eof_c) or
                            ((eof_r and do_sof_c) and not do_eof_c)           or
                            ((sof_to_eof_2_r and do_sof_c) and not do_eof_c)  or
                            ((sof_and_eof_r and do_sof_c) and not do_eof_c);


    next_data_c          <= (sof_to_data_r and not do_eof_c) or
                            (data_r and not do_eof_c);


    next_data_to_eof_1_c <= (sof_to_data_r and do_eof_c and channel_full_c) or
                            (data_r and do_eof_c and channel_full_c);


    next_data_to_eof_2_c <= data_to_eof_1_r;


    next_eof_c           <= (sof_to_data_r and do_eof_c and not channel_full_c) or
                            (data_r and do_eof_c and not channel_full_c);


    next_sof_to_eof_1_c  <= (idle_r and do_sof_c and do_eof_c and channel_full_c)          or
                            (data_to_eof_2_r and do_sof_c and do_eof_c and channel_full_c) or
                            (eof_r and do_sof_c and do_eof_c and channel_full_c)           or
                            (sof_to_eof_2_r and do_sof_c and do_eof_c and channel_full_c)  or
                            (sof_and_eof_r and do_sof_c and do_eof_c and channel_full_c);


    next_sof_to_eof_2_c  <= sof_to_eof_1_r;


    next_sof_and_eof_c   <= (idle_r and do_sof_c and do_eof_c and not channel_full_c)          or
                            (data_to_eof_2_r and do_sof_c and do_eof_c and not channel_full_c) or
                            (eof_r and do_sof_c and do_eof_c and not channel_full_c)           or
                            (sof_to_eof_2_r and do_sof_c and do_eof_c and not channel_full_c)  or
                            (sof_and_eof_r and do_sof_c and do_eof_c and not channel_full_c);


    -- We pipeline GEN_SCP because we are pipelining the datapath to leave travelling
    -- registers for the router; we must line up GEN_SCP with the appropriate data cycle.
    -- Drive the GEN_SCP signal when in an SOF state with the PDU state machine active.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                gen_scp_pipeline_r <= '0' after DLY;
                GEN_SCP_Buffer     <= '0' after DLY;

            else

                gen_scp_pipeline_r <= (sof_to_data_r or
                                      sof_to_eof_1_r or
                                      sof_and_eof_r) and
                                      pdu_ok_c after DLY;

                GEN_SCP_Buffer     <= gen_scp_pipeline_r after DLY;

            end if;

        end if;

    end process;


    -- We pipeline GEN_ECP because we are pipelining the datapath to leave travelling
    -- registers for the router; we must line up GEN_ECP with the appropriate data cycle.
    -- Drive the GEN_ECP signal when in an EOF state with the PDU state machine active.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                gen_ecp_pipeline_r <= '0' after DLY;
                GEN_ECP_Buffer     <= '0' after DLY;

            else

                gen_ecp_pipeline_r <= (data_to_eof_2_r or
                                      eof_r or
                                      sof_to_eof_2_r or
                                      sof_and_eof_r) and
                                      pdu_ok_c after DLY;



                GEN_ECP_Buffer     <= gen_ecp_pipeline_r after DLY;

            end if;

        end if;

    end process;


    -- TX_DST_RDY is the critical path in this module.  It must be deasserted (high)
    -- whenever an event occurs that prevents the pdu state machine from using the
    -- Aurora channel to transmit PDUs.

    tx_dst_rdy_n_c <= (next_data_to_eof_1_c and pdu_ok_c) or
                       not next_ufc_idle_c                or
                       DO_CC                              or
                       create_gap_for_scp_c               or
                      (next_sof_to_eof_1_c and pdu_ok_c)  or
                      (sof_to_eof_1_r and not pdu_ok_c)   or
                      (data_to_eof_1_r and not pdu_ok_c);


    -- SCP characters can only be added when the first lane position is open. After UFC messages,
    -- data gets deliberately held off for one cycle to create this gap.  No gap is added if no
    -- SCP character is needed.

    create_gap_for_scp_c <= (not ufc_idle_r and not ufc_header_r) and
                             not (data_r or
                             sof_to_data_r or
                             data_to_eof_1_r or
                             sof_to_eof_1_r);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            create_gap_for_scp_r <= create_gap_for_scp_c after DLY;

        end if;

    end process;


    -- We add extra travelling registers to the GEN_CC signal to ease routing.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                gen_cc_pipeline_r <= '0' after DLY;

            else

                gen_cc_pipeline_r <= do_cc_r after DLY;

            end if;

        end if;

    end process;


    -- The flops for the GEN_CC signal are replicated for timing and instantiated to allow us
    -- to set their value reliably on powerup.

    gen_cc_flop_0_i : FDR

        port map (

                    D => gen_cc_pipeline_r,
                    C => USER_CLK,
                    R => reset_i,
                    Q => GEN_CC_Buffer(0)

                 );


    gen_cc_flop_1_i : FDR

        port map (

                    D => gen_cc_pipeline_r,
                    C => USER_CLK,
                    R => reset_i,
                    Q => GEN_CC_Buffer(1)

                 );


    -- The UFC header state triggers the generation of SUF characters in the lane.  The signal is
    -- delayed to match up with the datapath delay so that SUF always appears on the cycle
    -- before the first data byte.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                suf_delay_1_r <= '0'          after DLY;

            else

                suf_delay_1_r <= ufc_header_r after DLY;

            end if;

        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if(CHANNEL_UP = '0') then

                suf_delay_2_r <= '0'           after DLY;

            else

                suf_delay_2_r <= suf_delay_1_r after DLY;

            end if;

        end if;

    end process;


    -- We add an extra travelling register to the GEN_SUF output for routability.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                gen_suf_pipeline_r <= '0' after DLY;
                GEN_SUF_Buffer     <= '0' after DLY;

            else

                gen_suf_pipeline_r <= suf_delay_2_r      after DLY;
                GEN_SUF_Buffer     <= gen_suf_pipeline_r after DLY;

            end if;

        end if;

    end process;


    -- Travelling registers must be added for the FC_NB signal so the pipeline for all
    -- signals stays matched.  FC_NB carries flow control codes to the Lane logic.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            fc_nb_pipeline_r <= fc_nb_c          after DLY;
            FC_NB_Buffer     <= fc_nb_pipeline_r after DLY;

        end if;

    end process;


    -- Flow control codes come from the UFC_TX_MS input delayed to match the UFC data delay.

    fc_nb_c <= delay_ms_2_r;


    -- The TX_DST_RDY_N signal is registered.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (CHANNEL_UP = '0') then

                TX_DST_RDY_N_Buffer <= '1' after DLY;

            else

                TX_DST_RDY_N_Buffer <= tx_dst_rdy_n_c after DLY;

            end if;

        end if;

    end process;


    -- Helper Logic

    -- SOF requests are valid when TX_SRC_RDY_N. TX_DST_RDY_N and TX_SOF_N are asserted

    do_sof_c <=     not TX_SRC_RDY_N            and
                    not TX_DST_RDY_N_Buffer     and
                    not TX_SOF_N;    


    -- EOF requests are valid when TX_SRC_RDY_N, TX_DST_RDY_N and TX_EOF_N are asserted

    do_eof_c <=     not TX_SRC_RDY_N            and
                    not TX_DST_RDY_N_Buffer     and
                    not TX_EOF_N;
                 
                 

    -- Freeze the PDU state machine when CCs must be handled.  Note that the PDU state machine
    -- does not freeze for UFCs - instead, logic is provided to allow the two datastreams
    -- to cooperate.

    pdu_ok_c <= not do_cc_r;


    -- Halt the flow of data through the datastream when the PDU state machine is frozen or
    -- when an SCP character has been delayed due to UFC collision.

    HALT_C_Buffer <= not pdu_ok_c;


    -- The aurora channel is 'full' if there is more than enough data to fit into
    -- a channel that is already carrying an SCP and an ECP character.

    channel_full_c <= std_bool(TX_REM > "011");

end RTL;
