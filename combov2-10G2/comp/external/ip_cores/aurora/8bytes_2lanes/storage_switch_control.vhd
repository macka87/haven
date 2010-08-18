--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: storage_switch_control.vhd,v $
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
------------------------------------------------------------------------------
--
--  STORAGE_SWITCH_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: STORAGE_SWITCH_CONTROL selects the input chunk for each storage chunk mux
--
--              This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
library aurora_8byte;

entity STORAGE_SWITCH_CONTROL is

    port (

            LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
            STORAGE_COUNT      : in std_logic_vector(0 to 2);
            END_STORAGE        : in std_logic;
            START_WITH_DATA    : in std_logic;
            STORAGE_SELECT     : out std_logic_vector(0 to 19);
            USER_CLK           : in std_logic

         );

end STORAGE_SWITCH_CONTROL;

architecture RTL of STORAGE_SWITCH_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal STORAGE_SELECT_Buffer : std_logic_vector(0 to 19);

-- Internal Register Declarations --

    signal end_r            : std_logic;
    signal lac_r            : std_logic_vector(0 to 2);
    signal stc_r            : std_logic_vector(0 to 2);
    signal storage_select_c : std_logic_vector(0 to 19);

-- Wire Declarations --

    signal overwrite_c   : std_logic;

begin

    STORAGE_SELECT <= STORAGE_SELECT_Buffer;

-- Main Body of Code --

    -- Combine the end signals.

    overwrite_c <= END_STORAGE or START_WITH_DATA;


    -- Generate switch signals --

    process (overwrite_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)

        variable vec : std_logic_vector(0 to 5);

    begin

        if (overwrite_c = '1') then

            storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

        else

            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;

            case vec is

                when "001000" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "001100" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "010000" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "010011" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(1,5);

                when "010100" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "011000" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "011010" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(2,5);

                when "011011" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(1,5);

                when "011100" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "100000" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when "100001" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(3,5);

                when "100010" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(2,5);

                when "100011" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(1,5);

                when "100100" =>

                    storage_select_c(0 to 4) <= conv_std_logic_vector(0,5);

                when others =>

                    storage_select_c(0 to 4) <= (others => 'X');

            end case;

        end if;

    end process;


    process (overwrite_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)

        variable vec : std_logic_vector(0 to 5);

    begin

        if (overwrite_c = '1') then

            storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

        else

            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;

            case vec is

                when "001000" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "001001" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(0,5);

                when "001100" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "010000" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "010001" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(0,5);

                when "010011" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(2,5);

                when "010100" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "011000" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "011001" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(0,5);

                when "011010" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(3,5);

                when "011011" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(2,5);

                when "011100" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "100000" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when "100010" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(3,5);

                when "100011" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(2,5);

                when "100100" =>

                    storage_select_c(5 to 9) <= conv_std_logic_vector(1,5);

                when others =>

                    storage_select_c(5 to 9) <= (others => 'X');

            end case;

        end if;

    end process;


    process (overwrite_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)

        variable vec : std_logic_vector(0 to 5);

    begin

        if (overwrite_c = '1') then

            storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

        else

            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;

            case vec is

                when "001000" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "001001" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(1,5);

                when "001010" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(0,5);

                when "001100" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "010000" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "010001" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(1,5);

                when "010010" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(0,5);

                when "010011" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(3,5);

                when "010100" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "011000" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "011001" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(1,5);

                when "011011" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(3,5);

                when "011100" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "100000" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when "100011" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(3,5);

                when "100100" =>

                    storage_select_c(10 to 14) <= conv_std_logic_vector(2,5);

                when others =>

                    storage_select_c(10 to 14) <= (others => 'X');

            end case;

        end if;

    end process;


    process (overwrite_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)

        variable vec : std_logic_vector(0 to 5);

    begin

        if (overwrite_c = '1') then

            storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

        else

            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;

            case vec is

                when "001000" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "001001" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(2,5);

                when "001010" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(1,5);

                when "001011" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(0,5);

                when "001100" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "010000" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "010001" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(2,5);

                when "010010" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(1,5);

                when "010100" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "011000" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "011001" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(2,5);

                when "011100" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "100000" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when "100100" =>

                    storage_select_c(15 to 19) <= conv_std_logic_vector(3,5);

                when others =>

                    storage_select_c(15 to 19) <= (others => 'X');

            end case;

        end if;

    end process;


    -- Register the storage select signals.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            STORAGE_SELECT_Buffer <= storage_select_c after DLY;

        end if;

    end process;

end RTL;
