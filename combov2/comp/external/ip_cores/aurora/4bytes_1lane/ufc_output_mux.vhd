--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_output_mux.vhd,v $
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
--  UFC_OUTPUT_MUX
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: the UFC_OUTPUT mux moves selected data from ufc storage and the
--               ufc barrel shifter to the ufc LocalLink output register. It
--               is made up of a series of muxes, one set for each lane. The
--               number of selections available for each mux increments with
--               lane position. The first lane has only one possible input, the
--               nth lane has N inputs.
--               Note that the 0th selection for each mux is connected to the
--               UFC storage input, and the remaining selections are connected
--               to the barrel-shifted input lanes in incrementing order.
--
--               This module supports 2 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_4byte1lane;

entity UFC_OUTPUT_MUX is

    port (

    -- Input interface to the muxes

            UFC_STORAGE_DATA    : in std_logic_vector(0 to 31);
            BARREL_SHIFTED_DATA : in std_logic_vector(0 to 31);
            MUX_SELECT          : in std_logic_vector(0 to 5);
            USER_CLK            : in std_logic;
            MUXED_DATA          : out std_logic_vector(0 to 31)

         );

end UFC_OUTPUT_MUX;

architecture RTL of UFC_OUTPUT_MUX is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal MUXED_DATA_Buffer : std_logic_vector(0 to 31);

-- Internal Register Declarations --

    signal muxed_data_c : std_logic_vector(0 to 31);

begin

    MUXED_DATA <= MUXED_DATA_Buffer;

-- Main Body of Code --

    -- We create a set of muxes for each lane.

    -- Lane 0 needs no mux, it is always connected to the storage lane.

    -- Mux for lane 1

    process (MUX_SELECT(3 to 5), UFC_STORAGE_DATA, BARREL_SHIFTED_DATA)

    begin

        case MUX_SELECT(3 to 5) is

            when "000" =>

                muxed_data_c(16 to 31) <= UFC_STORAGE_DATA(16 to 31);

            when "001" =>

                muxed_data_c(16 to 31) <= BARREL_SHIFTED_DATA(0 to 15);

            when others =>

                muxed_data_c(16 to 31) <= (others => 'X');

        end case;

    end process;


    -- Register the data.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            MUXED_DATA_Buffer <= UFC_STORAGE_DATA(0 to 15) & muxed_data_c(16 to 31) after DLY;

        end if;

    end process;

end RTL;
