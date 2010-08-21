--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: channel_error_detect.vhd,v $
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
--  CHANNEL_ERROR_DETECT
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  Description: the CHANNEL_ERROR_DETECT module monitors the error signals
--               from the Aurora Lanes in the channel.  If one or more errors
--               are detected, the error is reported as a channel error.  If
--               a hard error is detected, it sends a message to the channel
--               initialization state machine to reset the channel.
--
--               This module supports 2 2-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_4byte2lane;

entity CHANNEL_ERROR_DETECT is

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

end CHANNEL_ERROR_DETECT;

architecture RTL of CHANNEL_ERROR_DETECT is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal CHANNEL_SOFT_ERROR_Buffer : std_logic := '1';
    signal CHANNEL_HARD_ERROR_Buffer : std_logic := '1';
    signal RESET_CHANNEL_Buffer      : std_logic := '1';

-- Internal Register Declarations --

    signal soft_error_r : std_logic_vector(0 to 1);
    signal hard_error_r : std_logic_vector(0 to 1);

-- Wire Declarations --

    signal channel_soft_error_c : std_logic;
    signal channel_hard_error_c : std_logic;
    signal reset_channel_c      : std_logic;

begin

    CHANNEL_SOFT_ERROR <= CHANNEL_SOFT_ERROR_Buffer;
    CHANNEL_HARD_ERROR <= CHANNEL_HARD_ERROR_Buffer;
    RESET_CHANNEL      <= RESET_CHANNEL_Buffer;

-- Main Body of Code --

    -- Register all of the incoming error signals.  This is neccessary for timing.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            soft_error_r <= SOFT_ERROR after DLY;
            hard_error_r <= HARD_ERROR after DLY;

        end if;

    end process;


    -- Assert Channel soft error if any of the soft error signals are asserted.

    channel_soft_error_c <= soft_error_r(0) or
                            soft_error_r(1);

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            CHANNEL_SOFT_ERROR_Buffer <= channel_soft_error_c after DLY;

        end if;

    end process;


    -- Assert Channel hard error if any of the hard error signals are asserted.

    channel_hard_error_c <= hard_error_r(0) or
                            hard_error_r(1);

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            CHANNEL_HARD_ERROR_Buffer <= channel_hard_error_c after DLY;

        end if;

    end process;


    -- "reset_channel_r" is asserted when any of the LANE_UP signals are low.

    reset_channel_c <= not LANE_UP(0) or
                       not LANE_UP(1);

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            RESET_CHANNEL_Buffer <= reset_channel_c or POWER_DOWN after DLY;

        end if;

    end process;

end RTL;
