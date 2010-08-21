--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: output_switch_control.vhd,v $
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
--  OUTPUT_SWITCH_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: OUTPUT_SWITCH_CONTROL selects the input chunk for each muxed output chunk.
--
--               This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity OUTPUT_SWITCH_CONTROL is

    port (

            LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
            STORAGE_COUNT      : in std_logic_vector(0 to 2);
            END_STORAGE        : in std_logic;
            START_WITH_DATA    : in std_logic;
            OUTPUT_SELECT      : out std_logic_vector(0 to 19);
            USER_CLK           : in std_logic

         );

end OUTPUT_SWITCH_CONTROL;

architecture RTL of OUTPUT_SWITCH_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal OUTPUT_SELECT_Buffer : std_logic_vector(0 to 19);

-- Internal Register Declarations --

    signal output_select_c  : std_logic_vector(0 to 19);

-- Wire Declarations --

    signal take_storage_c   : std_logic;

begin

    OUTPUT_SELECT <= OUTPUT_SELECT_Buffer;


-- ***************************  Main Body of Code **************************** 

    -- Combine the End signals --

    take_storage_c <= END_STORAGE or START_WITH_DATA;


    -- Generate switch signals --

    -- Lane 0 is always connected to storage lane 0.

    -- Calculate switch setting for lane 1.
    process (take_storage_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)
        variable vec : std_logic_vector(0 to 5);
    begin
        if (take_storage_c = '1') then
            output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
        else
            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;
            case vec is
                when "000001" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(1,5);
                when "000010" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "000011" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "000100" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "001001" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(1,5);
                when "001010" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "001011" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "001100" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "010001" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(1,5);
                when "010010" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "010011" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "010100" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "011001" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(1,5);
                when "011010" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "011011" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "011100" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "100001" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(1,5);
                when "100010" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "100011" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when "100100" =>
                    output_select_c(5 to 9) <= conv_std_logic_vector(0,5);
                when others =>
                    output_select_c(5 to 9) <= (others => 'X');
            end case;
        end if;
    end process;

    -- Calculate switch setting for lane 2.
    process (take_storage_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)
        variable vec : std_logic_vector(0 to 5);
    begin
        if (take_storage_c = '1') then
            output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
        else
            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;
            case vec is
                when "000001" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(2,5);
                when "000010" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(1,5);
                when "000011" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "000100" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "001001" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(2,5);
                when "001010" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(1,5);
                when "001011" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "001100" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "010001" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(2,5);
                when "010010" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(1,5);
                when "010011" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "010100" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "011001" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(2,5);
                when "011010" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(1,5);
                when "011011" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "011100" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "100001" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(2,5);
                when "100010" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(1,5);
                when "100011" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when "100100" =>
                    output_select_c(10 to 14) <= conv_std_logic_vector(0,5);
                when others =>
                    output_select_c(10 to 14) <= (others => 'X');
            end case;
        end if;
    end process;

    -- Calculate switch setting for lane 3.
    process (take_storage_c, LEFT_ALIGNED_COUNT, STORAGE_COUNT)
        variable vec : std_logic_vector(0 to 5);
    begin
        if (take_storage_c = '1') then
            output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
        else
            vec := LEFT_ALIGNED_COUNT & STORAGE_COUNT;
            case vec is
                when "000001" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(3,5);
                when "000010" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(2,5);
                when "000011" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(1,5);
                when "000100" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
                when "001001" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(3,5);
                when "001010" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(2,5);
                when "001011" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(1,5);
                when "001100" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
                when "010001" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(3,5);
                when "010010" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(2,5);
                when "010011" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(1,5);
                when "010100" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
                when "011001" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(3,5);
                when "011010" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(2,5);
                when "011011" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(1,5);
                when "011100" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
                when "100001" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(3,5);
                when "100010" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(2,5);
                when "100011" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(1,5);
                when "100100" =>
                    output_select_c(15 to 19) <= conv_std_logic_vector(0,5);
                when others =>
                    output_select_c(15 to 19) <= (others => 'X');
            end case;
        end if;
    end process;


    -- Register the output select values.
    process (USER_CLK)
    begin
        if (USER_CLK 'event and USER_CLK = '1') then
            OUTPUT_SELECT_Buffer <= "00000" & output_select_c(5 to 19) after DLY;
        end if;
    end process;

end RTL;
