--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: storage_ce_control.vhd,v $
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
--  STORAGE_CE_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: the STORAGE_CE controls the enable signals of the the Storage register
--
--              This module supports 2 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;

entity STORAGE_CE_CONTROL is

    port (

            LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 1);
            STORAGE_COUNT      : in std_logic_vector(0 to 1);
            END_STORAGE        : in std_logic;
            START_WITH_DATA    : in std_logic;
            STORAGE_CE         : out std_logic_vector(0 to 1);
            USER_CLK           : in std_logic;
            RESET              : in std_logic

         );

end STORAGE_CE_CONTROL;

architecture RTL of STORAGE_CE_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal STORAGE_CE_Buffer : std_logic_vector(0 to 1);

-- Wire Declarations --

    signal overwrite_c  : std_logic;
    signal excess_c     : std_logic;
    signal ce_command_c : std_logic_vector(0 to 1);

begin

    STORAGE_CE <= STORAGE_CE_Buffer;

-- Main Body of Code --

    -- Combine the end signals.

    overwrite_c <= END_STORAGE or START_WITH_DATA;


    -- For each lane, determine the appropriate CE value.

    excess_c <= std_bool(( ("1" & LEFT_ALIGNED_COUNT) + ("1" & STORAGE_COUNT) ) > conv_std_logic_vector(2,3));

    ce_command_c(0) <= excess_c or std_bool(STORAGE_COUNT < conv_std_logic_vector(1,2)) or overwrite_c;
    ce_command_c(1) <= excess_c or std_bool(STORAGE_COUNT < conv_std_logic_vector(2,2)) or overwrite_c;


    -- Register the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                STORAGE_CE_Buffer <= (others => '0') after DLY;

            else

                STORAGE_CE_Buffer <= ce_command_c after DLY;

            end if;

        end if;

    end process;

end RTL;
