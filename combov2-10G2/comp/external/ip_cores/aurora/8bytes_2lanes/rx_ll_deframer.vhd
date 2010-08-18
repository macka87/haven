--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: rx_ll_deframer.vhd,v $
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
--  RX_LL_DEFRAMER
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: The RX_LL_DEFRAMER extracts framing information from incoming channel
--               data beats.  It detects the start and end of frames, invalidates data
--               that is outside of a frame, and generates signals that go to the Output
--               and Storage blocks to indicate when the end of a frame has been detected.
--
--               This module supports 4 4-byte lane designs.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_8byte;

-- synthesis translate_off
library UNISIM;
use UNISIM.all;
-- synthesis translate_on


entity RX_LL_DEFRAMER is

    port (

            PDU_DATA_V      : in std_logic_vector(0 to 3);
            PDU_SCP         : in std_logic_vector(0 to 3);
            PDU_ECP         : in std_logic_vector(0 to 3);
            USER_CLK        : in std_logic;
            RESET           : in std_logic;
            DEFRAMED_DATA_V : out std_logic_vector(0 to 3);
            IN_FRAME        : out std_logic_vector(0 to 3);
            AFTER_SCP       : out std_logic_vector(0 to 3)

         );

end RX_LL_DEFRAMER;

architecture RTL of RX_LL_DEFRAMER is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal DEFRAMED_DATA_V_Buffer : std_logic_vector(0 to 3);
    signal IN_FRAME_Buffer        : std_logic_vector(0 to 3);
    signal AFTER_SCP_Buffer       : std_logic_vector(0 to 3);

-- Internal Register Declarations --

    signal  in_frame_r : std_logic;
    signal  tied_gnd   : std_logic;
    signal  tied_vcc   : std_logic;

-- Wire Declarations --

    signal  carry_select_c     : std_logic_vector(0 to 3);
    signal  after_scp_select_c : std_logic_vector(0 to 3);
    signal  in_frame_c         : std_logic_vector(0 to 3);
    signal  after_scp_c        : std_logic_vector(0 to 3);

    component MUXCY

        port (

                O  : out std_logic;
                CI : in std_logic;
                DI : in std_logic;
                S  : in std_logic

             );

    end component;

begin

    DEFRAMED_DATA_V <= DEFRAMED_DATA_V_Buffer;
    IN_FRAME        <= IN_FRAME_Buffer;
    AFTER_SCP       <= AFTER_SCP_Buffer;

    tied_gnd <= '0';
    tied_vcc <= '1';

-- Main Body of Code --

    -- Mask Invalid data --

    -- Keep track of inframe status between clock cycles.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if(RESET = '1') then

                in_frame_r <= '0' after DLY;

            else

                in_frame_r <= in_frame_c(3) after DLY;

            end if;

        end if;

    end process;


    -- Combinatorial inframe detect for lane 0.

    carry_select_c(0) <= not PDU_ECP(0) and not PDU_SCP(0);

    in_frame_muxcy_0 : MUXCY

        port map (

                    O  => in_frame_c(0),
                    CI => in_frame_r,
                    DI => PDU_SCP(0),
                    S  => carry_select_c(0)

                 );


    -- Combinatorial inframe detect for 2-byte chunk 1.

    carry_select_c(1) <= not PDU_ECP(1) and not PDU_SCP(1);

    in_frame_muxcy_1 : MUXCY

        port map (

                    O  => in_frame_c(1),
                    CI => in_frame_c(0),
                    DI => PDU_SCP(1),
                    S  => carry_select_c(1)

                 );


    -- Combinatorial inframe detect for 2-byte chunk 2.

    carry_select_c(2) <= not PDU_ECP(2) and not PDU_SCP(2);

    in_frame_muxcy_2 : MUXCY

        port map (

                    O  => in_frame_c(2),
                    CI => in_frame_c(1),
                    DI => PDU_SCP(2),
                    S  => carry_select_c(2)

                 );


    -- Combinatorial inframe detect for 2-byte chunk 3.

    carry_select_c(3) <= not PDU_ECP(3) and not PDU_SCP(3);

    in_frame_muxcy_3 : MUXCY

        port map (

                    O  => in_frame_c(3),
                    CI => in_frame_c(2),
                    DI => PDU_SCP(3),
                    S  => carry_select_c(3)

                 );


    -- The data from a lane is valid if its valid signal is asserted and it is
    -- inside a frame.  Note the use of Bitwise AND.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                DEFRAMED_DATA_V_Buffer <= (others => '0') after DLY;

            else

                DEFRAMED_DATA_V_Buffer <= in_frame_c and PDU_DATA_V;

            end if;

        end if;

    end process;


    -- Register the inframe status.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                IN_FRAME_Buffer <= conv_std_logic_vector(0,4) after DLY;

            else

                IN_FRAME_Buffer <= in_frame_r & in_frame_c(0 to 2) after DLY;

            end if;

        end if;

    end process;


    -- Mark lanes that could contain data that occurs after an SCP. --

    -- Combinatorial data after start detect for lane 0.

    after_scp_select_c(0) <= not PDU_SCP(0);

    data_after_start_muxcy_0:MUXCY

        port map (

                    O  => after_scp_c(0),
                    CI => tied_gnd,
                    DI => tied_vcc,
                    S  => after_scp_select_c(0)

                 );


    -- Combinatorial data after start detect for lane1.

    after_scp_select_c(1) <= not PDU_SCP(1);

    data_after_start_muxcy_1:MUXCY

        port map (

                    O  => after_scp_c(1),
                    CI => after_scp_c(0),
                    DI => tied_vcc,
                    S  => after_scp_select_c(1)
                 );


    -- Combinatorial data after start detect for lane2.

    after_scp_select_c(2) <= not PDU_SCP(2);

    data_after_start_muxcy_2:MUXCY

        port map (

                    O  => after_scp_c(2),
                    CI => after_scp_c(1),
                    DI => tied_vcc,
                    S  => after_scp_select_c(2)
                 );


    -- Combinatorial data after start detect for lane3.

    after_scp_select_c(3) <= not PDU_SCP(3);

    data_after_start_muxcy_3:MUXCY

        port map (

                    O  => after_scp_c(3),
                    CI => after_scp_c(2),
                    DI => tied_vcc,
                    S  => after_scp_select_c(3)
                 );


    -- Register the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                AFTER_SCP_Buffer <= (others => '0');

            else

                AFTER_SCP_Buffer <= after_scp_c;

            end if;

        end if;

    end process;

end RTL;
