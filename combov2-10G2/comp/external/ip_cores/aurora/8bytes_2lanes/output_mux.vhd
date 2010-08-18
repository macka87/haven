--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: output_mux.vhd,v $
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
--  OUTPUT_MUX
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: The OUTPUT_MUX controls the flow of data to the LocalLink output
--               for user PDUs.
--
--               This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_8byte;

entity OUTPUT_MUX is

    port (

            STORAGE_DATA      : in std_logic_vector(0 to 63);
            LEFT_ALIGNED_DATA : in std_logic_vector(0 to 63);
            MUX_SELECT        : in std_logic_vector(0 to 19);
            USER_CLK          : in std_logic;
            OUTPUT_DATA       : out std_logic_vector(0 to 63)

         );

end OUTPUT_MUX;

architecture RTL of OUTPUT_MUX is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations

    signal OUTPUT_DATA_Buffer : std_logic_vector(0 to 63);

-- Internal Register Declarations --

    signal output_data_c : std_logic_vector(0 to 63);

begin

    OUTPUT_DATA <= OUTPUT_DATA_Buffer;

-- Main Body of Code --

    -- We create a set of muxes for each lane.  The number of inputs for each set of
    -- muxes increases as the lane index increases: lane 0 has one input only, the
    -- rightmost lane has 4 inputs.  Note that the 0th input connection
    -- is always to the storage lane with the same index as the output lane: the
    -- remaining inputs connect to the left_aligned data register, starting at index 0.

    -- Mux for lane 0

    process (MUX_SELECT(0 to 4), STORAGE_DATA)

    begin

        case MUX_SELECT(0 to 4) is

            when "00000" =>

                output_data_c(0 to 15) <= STORAGE_DATA(0 to 15);

            when others =>

                output_data_c(0 to 15) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 1

    process (MUX_SELECT(5 to 9), STORAGE_DATA, LEFT_ALIGNED_DATA)

    begin

        case MUX_SELECT(5 to 9) is

            when "00000" =>

                output_data_c(16 to 31) <= STORAGE_DATA(16 to 31);

            when "00001" =>

                output_data_c(16 to 31) <= LEFT_ALIGNED_DATA(0 to 15);

            when others =>

                output_data_c(16 to 31) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 2

    process (MUX_SELECT(10 to 14), STORAGE_DATA, LEFT_ALIGNED_DATA)

    begin

        case MUX_SELECT(10 to 14) is

            when "00000" =>

                output_data_c(32 to 47) <= STORAGE_DATA(32 to 47);

            when "00001" =>

                output_data_c(32 to 47) <= LEFT_ALIGNED_DATA(0 to 15);

            when "00010" =>

                output_data_c(32 to 47) <= LEFT_ALIGNED_DATA(16 to 31);

            when others =>

                output_data_c(32 to 47) <= (others => 'X');

        end case;

    end process;


    -- Mux for lane 3

    process (MUX_SELECT(15 to 19), STORAGE_DATA, LEFT_ALIGNED_DATA)

    begin

        case MUX_SELECT(15 to 19) is

            when "00000" =>

                output_data_c(48 to 63) <= STORAGE_DATA(48 to 63);

            when "00001" =>

                output_data_c(48 to 63) <= LEFT_ALIGNED_DATA(0 to 15);

            when "00010" =>

                output_data_c(48 to 63) <= LEFT_ALIGNED_DATA(16 to 31);

            when "00011" =>

                output_data_c(48 to 63) <= LEFT_ALIGNED_DATA(32 to 47);

            when others =>

                output_data_c(48 to 63) <= (others => 'X');

        end case;

    end process;


    -- Register the output data

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            OUTPUT_DATA_Buffer <= output_data_c after DLY;

        end if;

    end process;

end RTL;
