--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: valid_data_counter.vhd,v $
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
--  VALID_DATA_COUNTER
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: The VALID_DATA_COUNTER module counts the number of ones in a register filled
--               with ones and zeros.
--
--               This module supports 2 4-byte lane designs.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity VALID_DATA_COUNTER is

    port (

            PREVIOUS_STAGE_VALID : in std_logic_vector(0 to 1);
            USER_CLK             : in std_logic;
            RESET                : in std_logic;
            COUNT                : out std_logic_vector(0 to 1)

         );

end VALID_DATA_COUNTER;

architecture RTL of VALID_DATA_COUNTER is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal COUNT_Buffer : std_logic_vector(0 to 1);

-- Internal Register Declarations --

    signal  count_c   : std_logic_vector(0 to 1);

begin

    COUNT <= COUNT_Buffer;

-- Main Body of Code --

    -- Return the number of 1's in the binary representation of the input value.

    process (PREVIOUS_STAGE_VALID)

    begin

        count_c <= (

                        conv_std_logic_vector(0,2)
                      + PREVIOUS_STAGE_VALID(0)
                      + PREVIOUS_STAGE_VALID(1)

                   );

    end process;


    --Register the count

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                COUNT_Buffer <= (others => '0') after DLY;

            else

                COUNT_Buffer <= count_c after DLY;

            end if;

        end if;

    end process;


end RTL;
