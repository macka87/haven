--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_storage_count_control.vhd,v $
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
--  UFC_STORAGE_COUNT_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: UFC_STORAGE_COUNT_CONTROL sets the ufc storage count value for the next clock
--               cycle
--
--              This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity UFC_STORAGE_COUNT_CONTROL is

    port (

            BARREL_SHIFTED_COUNT : in std_logic_vector(0 to 2);
            UFC_START            : in std_logic;
            USER_CLK             : in std_logic;
            RESET                : in std_logic;
            UFC_STORAGE_COUNT    : out std_logic_vector(0 to 2)

         );

end UFC_STORAGE_COUNT_CONTROL;

architecture RTL of UFC_STORAGE_COUNT_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal UFC_STORAGE_COUNT_Buffer : std_logic_vector(0 to 2);

-- Internal Register Declarations --

    signal  storage_count_c : std_logic_vector(0 to 2);
    signal  storage_count_r : std_logic_vector(0 to 2);

-- Wire Declarations --

    signal  sum_c                : std_logic_vector(0 to 3);
    signal  reduced_sum_c        : std_logic_vector(0 to 3);
    signal  next_storage_count_c : std_logic_vector(0 to 2);

begin

    UFC_STORAGE_COUNT <= UFC_STORAGE_COUNT_Buffer;

-- Main Body of Code --

    -- Calculate the value that will be used for the switch.

    sum_c         <= conv_std_logic_vector(0,4) + BARREL_SHIFTED_COUNT + storage_count_r;
    reduced_sum_c <= sum_c - conv_std_logic_vector(4,4);

    next_storage_count_c <= reduced_sum_c(1 to 3) when (sum_c > conv_std_logic_vector(4,4)) else (others =>'0');


    process (UFC_START, next_storage_count_c, BARREL_SHIFTED_COUNT)

    begin

        if (UFC_START = '1') then

            storage_count_c <= BARREL_SHIFTED_COUNT;

        else

            storage_count_c <= next_storage_count_c;

        end if;

    end process;


    -- Register the storage count and make it available to the outside world.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if(RESET = '1') then

                storage_count_r <= (others => '0') after DLY;

            else

                storage_count_r <= storage_count_c after DLY;

            end if;

        end if;

    end process;


    UFC_STORAGE_COUNT_Buffer <= storage_count_r;

end RTL;
