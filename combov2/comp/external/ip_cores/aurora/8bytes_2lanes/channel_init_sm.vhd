--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: channel_init_sm.vhd,v $
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
--  CHANNEL_INIT_SM
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: the CHANNEL_INIT_SM module is a state machine for managing channel
--               bonding and verification.
--
--               The channel init state machine is reset until the lane up signals
--               of all the lanes that constitute the channel are asserted.  It then
--               requests channel bonding until the lanes have been bonded and
--               checks to make sure the bonding was successful.  Channel bonding is
--               skipped if there is only one lane in the channel.  If bonding is
--               unsuccessful, the lanes are reset.
--
--               After the bonding phase is complete, the state machine sends
--               verification sequences through the channel until it is clear that
--               the channel is ready to be used.  If verification is successful,
--               the CHANNEL_UP signal is asserted.  If it is unsuccessful, the
--               lanes are reset.
--
--               After CHANNEL_UP goes high, the state machine is quiescent, and will
--               reset only if one of the lanes goes down, a hard error is detected, or
--               a general reset is requested.
--
--               This module supports 2 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.NUMERIC_STD.all;
use WORK.AURORA.all;
library aurora_8byte;

-- synthesis translate_off

library UNISIM;
use UNISIM.all;

-- synthesis translate_on

entity CHANNEL_INIT_SM is
    generic (
            EXTEND_WATCHDOGS  : boolean := FALSE
    );
    port (

    -- MGT Interface

            CH_BOND_DONE      : in std_logic_vector(0 to 1);
            EN_CHAN_SYNC      : out std_logic;

    -- Aurora Lane Interface

            CHANNEL_BOND_LOAD : in std_logic_vector(0 to 1);
            GOT_A             : in std_logic_vector(0 to 7);
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

end CHANNEL_INIT_SM;

architecture RTL of CHANNEL_INIT_SM is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal EN_CHAN_SYNC_Buffer : std_logic;
    signal RESET_LANES_Buffer  : std_logic_vector(0 to 1);
    signal CHANNEL_UP_Buffer   : std_logic;
    signal START_RX_Buffer     : std_logic;
    signal GEN_VER_Buffer      : std_logic;

-- Internal Register Declarations --

    signal free_count_done_r       : std_logic;
    signal extend_watchdogs_n_r    : std_logic;
    signal verify_watchdog_r       : std_logic_vector(0 to 15);
    signal bonding_watchdog_r      : std_logic_vector(0 to 15);
    signal all_ch_bond_done_r      : std_logic;
    signal all_channel_bond_load_r : std_logic;
    signal bond_passed_r           : std_logic;
    signal good_as_r               : std_logic;
    signal bad_as_r                : std_logic;
    signal a_count_r               : unsigned(0 to 2);
    signal all_lanes_v_r           : std_logic;
    signal got_first_v_r           : std_logic;
    signal v_count_r               : std_logic_vector(0 to 15);
    signal bad_v_r                 : std_logic;
    signal rxver_count_r           : std_logic_vector(0 to 2);
    signal txver_count_r           : std_logic_vector(0 to 7);

    -- State registers

    signal wait_for_lane_up_r      : std_logic;
    signal channel_bond_r          : std_logic;
    signal check_bond_r            : std_logic;
    signal verify_r                : std_logic;
    signal ready_r                 : std_logic;

-- Wire Declarations --

    signal free_count_1_r          : std_logic;
    signal free_count_2_r          : std_logic;
    signal extend_watchdogs_1_r    : std_logic;
    signal extend_watchdogs_2_r    : std_logic;
    signal extend_watchdogs_n_c    : std_logic;    
    signal insert_ver_c            : std_logic;
    signal verify_watchdog_done_r  : std_logic;
    signal rxver_3d_done_r         : std_logic;
    signal txver_8d_done_r         : std_logic;
    signal reset_lanes_c           : std_logic;

    signal all_ch_bond_done_c      : std_logic;
    signal all_channel_bond_load_c : std_logic;
    signal en_chan_sync_c          : std_logic;
    signal all_as_c                : std_logic_vector(0 to 3);
    signal any_as_c                : std_logic_vector(0 to 3);
    signal four_as_r               : std_logic;
    signal bonding_watchdog_done_r : std_logic;
    signal all_lanes_v_c           : std_logic;

    -- Next state signals

    signal next_channel_bond_c     : std_logic;
    signal next_check_bond_c       : std_logic;
    signal next_verify_c           : std_logic;
    signal next_ready_c            : std_logic;

    -- VHDL utility signals

    signal  tied_to_vcc        : std_logic;
    signal  tied_to_gnd        : std_logic;

-- Component Declarations

    component SRL16
        generic (INIT : bit_vector := X"0000");
        port (

                Q   : out std_ulogic;
                A0  : in  std_ulogic;
                A1  : in  std_ulogic;
                A2  : in  std_ulogic;
                A3  : in  std_ulogic;
                CLK : in  std_ulogic;
                D   : in  std_ulogic

             );

    end component;

    component SRL16E
        generic (INIT : bit_vector := X"0000");
        port (

                Q   : out std_ulogic;
                A0  : in  std_ulogic;
                A1  : in  std_ulogic;
                A2  : in  std_ulogic;
                A3  : in  std_ulogic;
                CE  : in  std_ulogic;
                CLK : in  std_ulogic;
                D   : in  std_ulogic

             );

    end component;

    component FD
        generic (INIT : bit := '0');
        port (

                Q : out std_ulogic;
                C : in  std_ulogic;
                D : in  std_ulogic

             );

    end component;

begin

    EN_CHAN_SYNC <= EN_CHAN_SYNC_Buffer;
    RESET_LANES  <= RESET_LANES_Buffer;
    CHANNEL_UP   <= CHANNEL_UP_Buffer;
    START_RX     <= START_RX_Buffer;
    GEN_VER      <= GEN_VER_Buffer;

    tied_to_vcc  <= '1';
    tied_to_gnd  <= '0';

-- Main Body of Code --

    -- Main state machine for bonding and verification --

    -- State registers

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or RESET_CHANNEL) = '1') then

                wait_for_lane_up_r <= '1' after DLY;
                channel_bond_r     <= '0' after DLY;
                check_bond_r       <= '0' after DLY;
                verify_r           <= '0' after DLY;
                ready_r            <= '0' after DLY;

            else

                wait_for_lane_up_r <= '0' after DLY;
                channel_bond_r     <= next_channel_bond_c after DLY;
                check_bond_r       <= next_check_bond_c after DLY;
                verify_r           <= next_verify_c after DLY;
                ready_r            <= next_ready_c after DLY;

            end if;

        end if;

    end process;


    -- Next state logic

    next_channel_bond_c <= wait_for_lane_up_r or
                           (channel_bond_r and not bond_passed_r) or
                           (check_bond_r and bad_as_r);

    next_check_bond_c   <= (channel_bond_r and bond_passed_r ) or
                           ((check_bond_r and not four_as_r) and not bad_as_r);

    next_verify_c       <= ((check_bond_r and four_as_r) and not bad_as_r) or
                           (verify_r and (not rxver_3d_done_r or not txver_8d_done_r));

    next_ready_c        <= ((verify_r and txver_8d_done_r) and rxver_3d_done_r) or
                           ready_r;


    -- Output Logic

    -- Channel up is high as long as the Global Logic is in the ready state.

    CHANNEL_UP_Buffer <= ready_r;


    -- Turn the receive engine on as soon as all the lanes are up.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                START_RX_Buffer <= '0' after DLY;

            else

                START_RX_Buffer <= not wait_for_lane_up_r after DLY;

            end if;

        end if;

    end process;


    -- Generate the Verification sequence when in the verify state.

    GEN_VER_Buffer <= verify_r;


    -- Channel Reset --

    -- Some problems during channel bonding and verification require the lanes to
    -- be reset.  When this happens, we assert the Reset Lanes signal, which gets
    -- sent to all Aurora Lanes.  When the Aurora Lanes reset, their LANE_UP signals
    -- go down.  This causes the Channel Error Detector to assert the Reset Channel
    -- signal.

    reset_lanes_c <= (verify_r and verify_watchdog_done_r) or
                     ((verify_r and bad_v_r) and not rxver_3d_done_r) or
                     (channel_bond_r and bonding_watchdog_done_r) or
                     (check_bond_r and bonding_watchdog_done_r) or
                     (RESET_CHANNEL and not wait_for_lane_up_r) or
                     RESET;


    reset_lanes_flop_0_i : FD
        generic map (INIT => '1')
        port map (

                    D => reset_lanes_c,
                    C => USER_CLK,
                    Q => RESET_LANES_Buffer(0)

                 );


    reset_lanes_flop_1_i : FD
        generic map (INIT => '1')
        port map (

                    D => reset_lanes_c,
                    C => USER_CLK,
                    Q => RESET_LANES_Buffer(1)

                 );


    -- Watchdog timers --

    -- We create a free counter out of SRLs to count large values without excessive cost.

    free_count_1_i : SRL16
        generic map (INIT => X"8000")
        port map (

                    Q   => free_count_1_r,
                    A0  => tied_to_vcc,
                    A1  => tied_to_vcc,
                    A2  => tied_to_vcc,
                    A3  => tied_to_vcc,
                    CLK => USER_CLK,
                    D   => free_count_1_r

                 );


    free_count_2_i : SRL16E
        generic map (INIT => X"8000")
        port map (

                    Q   => free_count_2_r,
                    A0  => tied_to_vcc,
                    A1  => tied_to_vcc,
                    A2  => tied_to_vcc,
                    A3  => tied_to_vcc,
                    CLK => USER_CLK,
                    CE  => free_count_1_r,
                    D   => free_count_2_r

                 );


    -- The watchdog extention SRLs are used to multiply the free count by 32
    extend_watchdogs_1_i :SRL16E 
    port map
    (
        Q       =>  extend_watchdogs_1_r,
        A0      =>  tied_to_vcc,
        A1      =>  tied_to_vcc,
        A2      =>  tied_to_vcc,
        A3      =>  tied_to_vcc,
        CLK     =>  USER_CLK,
        CE      =>  free_count_1_r,
        D       =>  extend_watchdogs_n_c
    );
    
    
    extend_watchdogs_2_i :SRL16E 
    port map
    (
        Q       =>  extend_watchdogs_2_r,
        A0      =>  tied_to_vcc,
        A1      =>  tied_to_vcc,
        A2      =>  tied_to_vcc,
        A3      =>  tied_to_vcc,
        CLK     =>  USER_CLK,
        CE      =>  free_count_1_r,
        D       =>  extend_watchdogs_1_r
    );    
    
    extend_watchdogs_n_c <=   not extend_watchdogs_2_r;
    
    process (USER_CLK)
    begin
        if( USER_CLK'event and USER_CLK='1') then
            extend_watchdogs_n_r    <=  extend_watchdogs_n_c;
        end if;
    end process;




    -- Finally we have logic hat registers a pulse when both the inner and the
    -- outer SRLs have a bit in their last position.  This should map to carry logic
    -- and a register.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then
            if(EXTEND_WATCHDOGS) then
                free_count_done_r <= extend_watchdogs_2_r and extend_watchdogs_n_r after DLY;
            else
                free_count_done_r <= free_count_2_r and free_count_1_r after DLY;
            end if;
        end if;

    end process;


    -- We use the free running count as a CE for the verify watchdog.  The
    -- count runs continuously so the watchdog will vary between a count of 4096
    -- and 3840 cycles - acceptable for this application.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((free_count_done_r or not verify_r) = '1') then

                verify_watchdog_r <= verify_r & verify_watchdog_r(0 to 14) after DLY;

            end if;

        end if;

    end process;


    verify_watchdog_done_r <= verify_watchdog_r(15);


    -- The channel bonding watchdog is triggered when the channel_bond_load
    -- signal has been asserted 16 times in the channel_bonding state without
    -- continuing or resetting.  If this happens, we reset the lanes.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((not (channel_bond_r or check_bond_r) or all_channel_bond_load_r or free_count_done_r) = '1') then

                bonding_watchdog_r <= channel_bond_r & bonding_watchdog_r(0 to 14) after DLY;

            end if;

        end if;

    end process;


    bonding_watchdog_done_r <= bonding_watchdog_r(15);


    -- Channel Bonding --

    -- We send the EN_CHAN_SYNC signal to the master lane.

    en_chan_sync_flop_i : FD

        generic map (INIT => '0')

        port map (

                    D => channel_bond_r,
                    C => USER_CLK,
                    Q => EN_CHAN_SYNC_Buffer

                 );


    -- This first wide AND gate collects the CH_BOND_DONE signals.  We register the
    -- output of the AND gate.  Note that register is a one shot that is reset
    -- only when the state changes.

    all_ch_bond_done_c <= CH_BOND_DONE(0) and
                          CH_BOND_DONE(1);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (channel_bond_r = '0') then

                all_ch_bond_done_r <= '0' after DLY;

            else

                if (all_ch_bond_done_c = '1') then

                    all_ch_bond_done_r <= '1' after DLY;

                end if;

            end if;

        end if;

    end process;


    -- This wide AND gate collects the CHANNEL_BOND_LOAD signals from each lane.
    -- We register the output of the AND gate.

    all_channel_bond_load_c <= CHANNEL_BOND_LOAD(0) and
                               CHANNEL_BOND_LOAD(1);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            all_channel_bond_load_r <= all_channel_bond_load_c after DLY;

        end if;

    end process;


    -- Assert bond_passed_r if all_channel_bond_load_r goes high with all_ch_bond_done_r high.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            bond_passed_r <= all_ch_bond_done_r and all_channel_bond_load_r after DLY;

        end if;

    end process;


    -- Good_as_r is asserted as long as no bad As are detected.  Bad As are As that do
    -- not arrive with the rest of the As in the channel.

    all_as_c(0) <= GOT_A(0) and
                   GOT_A(4);


    all_as_c(1) <= GOT_A(1) and
                   GOT_A(5);


    all_as_c(2) <= GOT_A(2) and
                   GOT_A(6);


    all_as_c(3) <= GOT_A(3) and
                   GOT_A(7);


    any_as_c(0) <= GOT_A(0) or
                   GOT_A(4);


    any_as_c(1) <= GOT_A(1) or
                   GOT_A(5);


    any_as_c(2) <= GOT_A(2) or
                   GOT_A(6);


    any_as_c(3) <= GOT_A(3) or
                   GOT_A(7);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            good_as_r <= all_as_c(0) or all_as_c(1) or all_as_c(2) or all_as_c(3) after DLY;

        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            bad_as_r <= std_bool((any_as_c and not all_as_c) /= "0000") after DLY;

        end if;

    end process;


    -- Four_as_r is asserted when you get 4 consecutive good As in check_bond state.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (check_bond_r = '0') then

                a_count_r <= "000" after DLY;

            else

                if (good_as_r = '1') then

                    a_count_r <= a_count_r + "001" after DLY;

                end if;

            end if;

        end if;

    end process;


    four_as_r <= a_count_r(0);


    -- Verification --

    -- Vs need to appear on all lanes simultaneously.

    all_lanes_v_c <= GOT_V(0) and
                     GOT_V(1);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            all_lanes_v_r <= all_lanes_v_c after DLY;

        end if;

    end process;


    -- Vs need to be decoded by the aurora lane and then checked by the
    -- Global logic.  They must appear periodically.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (verify_r = '0') then

                got_first_v_r <= '0' after DLY;

            else

                if (all_lanes_v_r = '1') then

                    got_first_v_r <= '1' after DLY;

                end if;

            end if;

        end if;

    end process;


    insert_ver_c <= (all_lanes_v_r and not got_first_v_r) or (v_count_r(15) and verify_r);


    -- Shift register for measuring the time between V counts.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            v_count_r <= insert_ver_c & v_count_r(0 to 14) after DLY;

        end if;

    end process;


    -- Assert bad_v_r if a V does not arrive when expected.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            bad_v_r <= (v_count_r(15) xor all_lanes_v_r) and got_first_v_r after DLY;

        end if;

    end process;


    -- Count the number of Ver sequences received.  You're done after you receive four.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (((v_count_r(15) and all_lanes_v_r) or not verify_r) = '1') then

                rxver_count_r <= verify_r & rxver_count_r(0 to 1) after DLY;

            end if;

        end if;

    end process;


    rxver_3d_done_r <= rxver_count_r(2);


    -- Count the number of Ver sequences transmitted. You're done after you send eight.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((DID_VER or not verify_r) = '1') then

                txver_count_r <= verify_r & txver_count_r(0 to 6) after DLY;

            end if;

        end if;

    end process;


    txver_8d_done_r <= txver_count_r(7);

end RTL;
