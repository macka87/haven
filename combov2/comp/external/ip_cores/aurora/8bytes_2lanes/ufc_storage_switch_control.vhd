--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_storage_switch_control.vhd,v $
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
--  UFC_STORAGE_SWITCH_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: UFC_STORAGE_SWITCH_CONTROL selects the input chunk for each ufc storage chunk mux
--
--              This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;
library aurora_8byte;

entity UFC_STORAGE_SWITCH_CONTROL is

    port (

            BARREL_SHIFTED_COUNT : in std_logic_vector(0 to 2);
            UFC_STORAGE_COUNT    : in std_logic_vector(0 to 2);
            UFC_START            : in std_logic;
            USER_CLK             : in std_logic;
            UFC_STORAGE_SELECT   : out std_logic_vector(0 to 11)

         );

end UFC_STORAGE_SWITCH_CONTROL;

architecture RTL of UFC_STORAGE_SWITCH_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations

    signal UFC_STORAGE_SELECT_Buffer : std_logic_vector(0 to 11);

-- Internal Register Declarations --

    signal ufc_storage_select_c : std_logic_vector(0 to 11);

-- Wire Declarations --

    signal sum_c            : std_logic_vector(0 to 3);
    signal overflow_c       : std_logic;
    signal overflow_value_c : std_logic_vector(0 to 15);

begin

    UFC_STORAGE_SELECT <= UFC_STORAGE_SELECT_Buffer;

-- Main Body of Code --

    sum_c      <= "0000" + BARREL_SHIFTED_COUNT + UFC_STORAGE_COUNT;
    overflow_c <= std_bool(sum_c > conv_std_logic_vector(4,4)) and not UFC_START;


    -- Generate switch signals --

    -- Select for Lane 0

    overflow_value_c(0 to 3) <= conv_std_logic_vector(4,4) - UFC_STORAGE_COUNT;

    process (overflow_c, overflow_value_c)

    begin

        if (overflow_c = '1') then

            ufc_storage_select_c(0 to 2) <= overflow_value_c(1 to 3);

        else

            ufc_storage_select_c(0 to 2) <= conv_std_logic_vector(0,3);

        end if;

    end process;


    -- Select for Lane 1

    overflow_value_c(4 to 7) <= conv_std_logic_vector(5,4) - UFC_STORAGE_COUNT;

    process (overflow_c, overflow_value_c)

    begin

        if (overflow_c = '1') then

            ufc_storage_select_c(3 to 5) <= overflow_value_c(5 to 7);

        else

            ufc_storage_select_c(3 to 5) <= conv_std_logic_vector(1,3);

        end if;

    end process;


    -- Select for Lane 2

    overflow_value_c(8 to 11) <= conv_std_logic_vector(6,4) - UFC_STORAGE_COUNT;

    process (overflow_c, overflow_value_c)

    begin

        if (overflow_c = '1') then

            ufc_storage_select_c(6 to 8) <= overflow_value_c(9 to 11);

        else

            ufc_storage_select_c(6 to 8) <= conv_std_logic_vector(2,3);

        end if;

    end process;


    -- Select for Lane 3

    overflow_value_c(12 to 15) <= conv_std_logic_vector(7,4) - UFC_STORAGE_COUNT;

    process (overflow_c, overflow_value_c)

    begin

        if (overflow_c = '1') then

            ufc_storage_select_c(9 to 11) <= overflow_value_c(13 to 15);

        else

            ufc_storage_select_c(9 to 11) <= conv_std_logic_vector(3,3);

        end if;

    end process;


    -- Register the storage selection.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            UFC_STORAGE_SELECT_Buffer <= ufc_storage_select_c after DLY;

        end if;

    end process;

end RTL;
