--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: storage_count_control.vhd,v $
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
--  STORAGE_COUNT_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: STORAGE_COUNT_CONTROL sets the storage count value for the next clock
--               cycle
--
--              This module supports 2 2-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;
library aurora_4byte2lane;

entity STORAGE_COUNT_CONTROL is

    port (

            LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 1);
            END_STORAGE        : in std_logic;
            START_WITH_DATA    : in std_logic;
            FRAME_ERROR        : in std_logic;
            STORAGE_COUNT      : out std_logic_vector(0 to 1);
            USER_CLK           : in std_logic;
            RESET              : in std_logic

         );

end STORAGE_COUNT_CONTROL;

architecture RTL of STORAGE_COUNT_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal STORAGE_COUNT_Buffer : std_logic_vector(0 to 1);

-- Internal Register Declarations --

    signal storage_count_c : std_logic_vector(0 to 1);
    signal storage_count_r : std_logic_vector(0 to 1);

-- Wire Declarations --

    signal overwrite_c : std_logic;
    signal sum_c       : std_logic_vector(0 to 2);
    signal remainder_c : std_logic_vector(0 to 2);
    signal overflow_c  : std_logic;

begin

    STORAGE_COUNT <= STORAGE_COUNT_Buffer;

-- Main Body of Code --

    -- Calculate the value that will be used for the switch.

    sum_c       <= conv_std_logic_vector(0,3) + LEFT_ALIGNED_COUNT + storage_count_r;
    remainder_c <= sum_c - conv_std_logic_vector(2,3);

    overwrite_c <= END_STORAGE or START_WITH_DATA;
    overflow_c  <= std_bool(sum_c > conv_std_logic_vector(2,3));


    process (overwrite_c, overflow_c, sum_c, remainder_c, LEFT_ALIGNED_COUNT)

        variable vec : std_logic_vector(0 to 1);

    begin

        vec := overwrite_c & overflow_c;

        case vec is

            when "00" =>

                storage_count_c <= sum_c(1 to 2);

            when "01" =>

                storage_count_c <= remainder_c(1 to 2);

            when "10" =>

                storage_count_c <= LEFT_ALIGNED_COUNT;

            when "11" =>

                storage_count_c <= LEFT_ALIGNED_COUNT;

            when others =>

                storage_count_c <= (others => 'X');

        end case;

    end process;


    -- Register the Storage Count for the next cycle.

    process (USER_CLK)

    begin

        if (USER_CLK'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                storage_count_r <= (others => '0') after DLY;

            else

                storage_count_r <=  storage_count_c after DLY;

            end if;

        end if;

    end process;


    -- Make the output of the storage count register available to other modules.

    STORAGE_COUNT_Buffer <= storage_count_r;

end RTL;
