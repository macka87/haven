--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_storage_mux.vhd,v $
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
--  UFC_STORAGE_MUX
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: the UFC_STORAGE_MUX is a series of N:1 muxes used to determine
--               which input lanes feed which storage register.
--
--
--               This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_8byte;

entity UFC_STORAGE_MUX is

    port (

    -- Input interface to the muxes

            RAW_DATA   : in std_logic_vector(0 to 63);
            MUX_SELECT : in std_logic_vector(0 to 11);
            USER_CLK   : in std_logic;

    -- Mux output

            MUXED_DATA : out std_logic_vector(0 to 63)

         );

end UFC_STORAGE_MUX;

architecture RTL of UFC_STORAGE_MUX is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations

    signal MUXED_DATA_Buffer : std_logic_vector(0 to 63);

-- Internal Register Declarations --

    signal  muxed_data_c : std_logic_vector(0 to 63);

begin

    MUXED_DATA <= MUXED_DATA_Buffer;

-- Main Body of Code --

    -- We create muxes for each lane

    -- Mux for lane 0

    process (MUX_SELECT(0 to 2), RAW_DATA)

    begin

        case MUX_SELECT(0 to 2) is

            when "000" =>

                muxed_data_c(0 to 15) <= RAW_DATA(0 to 15);

            when "001" =>

                muxed_data_c(0 to 15) <= RAW_DATA(16 to 31);

            when "010" =>

                muxed_data_c(0 to 15) <= RAW_DATA(32 to 47);

            when "011" =>

                muxed_data_c(0 to 15) <= RAW_DATA(48 to 63);

            when others =>

                muxed_data_c(0 to 15) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 1

    process (MUX_SELECT(3 to 5), RAW_DATA)

    begin

        case MUX_SELECT(3 to 5) is

            when "000" =>

                muxed_data_c(16 to 31) <= RAW_DATA(0 to 15);

            when "001" =>

                muxed_data_c(16 to 31) <= RAW_DATA(16 to 31);

            when "010" =>

                muxed_data_c(16 to 31) <= RAW_DATA(32 to 47);

            when "011" =>

                muxed_data_c(16 to 31) <= RAW_DATA(48 to 63);

            when others =>

                muxed_data_c(16 to 31) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 2

    process (MUX_SELECT(6 to 8), RAW_DATA)

    begin

        case MUX_SELECT(6 to 8) is

            when "000" =>

                muxed_data_c(32 to 47) <= RAW_DATA(0 to 15);

            when "001" =>

                muxed_data_c(32 to 47) <= RAW_DATA(16 to 31);

            when "010" =>

                muxed_data_c(32 to 47) <= RAW_DATA(32 to 47);

            when "011" =>

                muxed_data_c(32 to 47) <= RAW_DATA(48 to 63);

            when others =>

                muxed_data_c(32 to 47) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 3

    process (MUX_SELECT(9 to 11), RAW_DATA)

    begin

        case MUX_SELECT(9 to 11) is

            when "000" =>

                muxed_data_c(48 to 63) <= RAW_DATA(0 to 15);

            when "001" =>

                muxed_data_c(48 to 63) <= RAW_DATA(16 to 31);

            when "010" =>

                muxed_data_c(48 to 63) <= RAW_DATA(32 to 47);

            when "011" =>

                muxed_data_c(48 to 63) <= RAW_DATA(48 to 63);

            when others =>

                muxed_data_c(48 to 63) <= (others => 'X');

        end case;

    end process;


    -- Register the data

    process (USER_CLK)

    begin

        if (USER_CLK'event and USER_CLK = '1') then

            MUXED_DATA_Buffer <= muxed_data_c after DLY;

        end if;

    end process;

end RTL;


