--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: storage_mux.vhd,v $
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
--  STORAGE_MUX
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: The STORAGE_MUX has a set of 16 bit muxes to control the
--               flow of data.  Every output position has its own N:1 mux.
--
--               This module supports 4 4-byte lane designs.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;

entity STORAGE_MUX is

    port (

            RAW_DATA     : in std_logic_vector(0 to 63);
            MUX_SELECT   : in std_logic_vector(0 to 19);
            STORAGE_CE   : in std_logic_vector(0 to 3);
            USER_CLK     : in std_logic;
            STORAGE_DATA : out std_logic_vector(0 to 63)

         );

end STORAGE_MUX;

architecture RTL of STORAGE_MUX is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal STORAGE_DATA_Buffer : std_logic_vector(0 to 63);

-- Internal Register Declarations --

    signal storage_data_c : std_logic_vector(0 to 63);

begin

    STORAGE_DATA <= STORAGE_DATA_Buffer;

-- Main Body of Code --

    -- Each lane has a set of 16 N:1 muxes connected to all the raw data lanes.

    -- Muxes for Lane 0

    process (MUX_SELECT(0 to 4), RAW_DATA)

    begin

        case MUX_SELECT(0 to 4) is

            when "00000" =>

                storage_data_c(0 to 15) <= RAW_DATA(0 to 15);

            when "00001" =>

                storage_data_c(0 to 15) <= RAW_DATA(16 to 31);

            when "00010" =>

                storage_data_c(0 to 15) <= RAW_DATA(32 to 47);

            when "00011" =>

                storage_data_c(0 to 15) <= RAW_DATA(48 to 63);

            when others =>

                storage_data_c(0 to 15) <= (others => 'X');

        end case;

    end process;


    -- Muxes for Lane 1

    process (MUX_SELECT(5 to 9), RAW_DATA)

    begin

        case MUX_SELECT(5 to 9) is

            when "00000" =>

                storage_data_c(16 to 31) <= RAW_DATA(0 to 15);

            when "00001" =>

                storage_data_c(16 to 31) <= RAW_DATA(16 to 31);

            when "00010" =>

                storage_data_c(16 to 31) <= RAW_DATA(32 to 47);

            when "00011" =>

                storage_data_c(16 to 31) <= RAW_DATA(48 to 63);

            when others =>

                storage_data_c(16 to 31) <= (others => 'X');

        end case;

    end process;


    -- Muxes for Lane 2

    process (MUX_SELECT(10 to 14), RAW_DATA)

    begin

        case MUX_SELECT(10 to 14) is

            when "00000" =>

                storage_data_c(32 to 47) <= RAW_DATA(0 to 15);

            when "00001" =>

                storage_data_c(32 to 47) <= RAW_DATA(16 to 31);

            when "00010" =>

                storage_data_c(32 to 47) <= RAW_DATA(32 to 47);

            when "00011" =>

                storage_data_c(32 to 47) <= RAW_DATA(48 to 63);

            when others =>

                storage_data_c(32 to 47) <= (others => 'X');

        end case;

    end process;


    -- Muxes for Lane 3

    process (MUX_SELECT(15 to 19), RAW_DATA)

    begin

        case MUX_SELECT(15 to 19) is

            when "00000" =>

                storage_data_c(48 to 63) <= RAW_DATA(0 to 15);

            when "00001" =>

                storage_data_c(48 to 63) <= RAW_DATA(16 to 31);

            when "00010" =>

                storage_data_c(48 to 63) <= RAW_DATA(32 to 47);

            when "00011" =>

                storage_data_c(48 to 63) <= RAW_DATA(48 to 63);

            when others =>

                storage_data_c(48 to 63) <= (others => 'X');

        end case;

    end process;


    -- Register the stored data.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (STORAGE_CE(0) = '1') then

                STORAGE_DATA_Buffer(0 to 15) <= storage_data_c(0 to 15) after DLY;

            end if;

            if (STORAGE_CE(1) = '1') then

                STORAGE_DATA_Buffer(16 to 31) <= storage_data_c(16 to 31) after DLY;

            end if;

            if (STORAGE_CE(2) = '1') then

                STORAGE_DATA_Buffer(32 to 47) <= storage_data_c(32 to 47) after DLY;

            end if;

            if (STORAGE_CE(3) = '1') then

                STORAGE_DATA_Buffer(48 to 63) <= storage_data_c(48 to 63) after DLY;

            end if;

        end if;

    end process;

end RTL;
