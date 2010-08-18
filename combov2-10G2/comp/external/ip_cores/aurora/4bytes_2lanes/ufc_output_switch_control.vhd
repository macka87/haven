--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_output_switch_control.vhd,v $
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
--  UFC_OUTPUT_SWITCH_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: UFC_OUTPUT_SWITCH_CONTROL selects the input chunk for each ufc output mux
--
--              This module supports 2 2-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
library aurora_4byte2lane;

entity UFC_OUTPUT_SWITCH_CONTROL is

    port (

            UFC_STORAGE_COUNT : in std_logic_vector(0 to 1);
            USER_CLK          : in std_logic;
            UFC_OUTPUT_SELECT : out std_logic_vector(0 to 5)

         );

end UFC_OUTPUT_SWITCH_CONTROL;

architecture RTL of UFC_OUTPUT_SWITCH_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations

    signal UFC_OUTPUT_SELECT_Buffer : std_logic_vector(0 to 5);

-- Internal Register Declarations --

    signal ufc_output_select_c : std_logic_vector(0 to 5);

-- Wire Declarations --

    signal overflow_c : std_logic;
    signal sum_c      : std_logic_vector(0 to 7);

begin

    UFC_OUTPUT_SELECT <= UFC_OUTPUT_SELECT_Buffer;

-- Main Body of Code --

    -- Generate switch signals --

    -- Select for Lane 0

    sum_c(0 to 3) <= conv_std_logic_vector(1,4) - UFC_STORAGE_COUNT;

    process (sum_c)

    begin

        if (sum_c(0) = '1') then

            ufc_output_select_c(0 to 2) <= (others => '0');

        else

            ufc_output_select_c(0 to 2) <= sum_c(1 to 3);

        end if;

    end process;


    -- Select for Lane 1

    sum_c(4 to 7) <= conv_std_logic_vector(2,4) - UFC_STORAGE_COUNT;

    process (sum_c)

    begin

        if (sum_c(4) = '1') then

            ufc_output_select_c(3 to 5) <= (others => '0');

        else

            ufc_output_select_c(3 to 5) <= sum_c(5 to 7);

        end if;

    end process;


    -- Register the output

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            UFC_OUTPUT_SELECT_Buffer <= ufc_output_select_c after DLY;

        end if;

    end process;

end RTL;
