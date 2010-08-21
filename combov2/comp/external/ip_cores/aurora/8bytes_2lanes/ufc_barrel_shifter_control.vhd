--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_barrel_shifter_control.vhd,v $
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
--  UFC_BARREL_SHIFTER_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: this module controls the UFC barrel shifter
--
--               This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_8byte;

entity UFC_BARREL_SHIFTER_CONTROL is

    port (

            UFC_MESSAGE_START      : in std_logic_vector(0 to 3);
            USER_CLK               : in std_logic;
            BARREL_SHIFTER_CONTROL : out std_logic_vector(0 to 2)

         );

end UFC_BARREL_SHIFTER_CONTROL;

architecture RTL of UFC_BARREL_SHIFTER_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations

    signal BARREL_SHIFTER_CONTROL_Buffer : std_logic_vector(0 to 2);

-- Internal Register Declarations --

    signal  barrel_shifter_control_i : std_logic_vector(0 to 2);

begin

    BARREL_SHIFTER_CONTROL <= BARREL_SHIFTER_CONTROL_Buffer;

-- Main Body of Code --

    -- Control for barrel shifting --

    -- Generate a barrel shift control number, which indicates how far to the left all the
    -- lane data should be shifted.

    process (UFC_MESSAGE_START)

    begin

        if (UFC_MESSAGE_START(0) = '1') then

            barrel_shifter_control_i <= conv_std_logic_vector(1,3);

        elsif (UFC_MESSAGE_START(1) = '1') then

            barrel_shifter_control_i <= conv_std_logic_vector(2,3);

        elsif (UFC_MESSAGE_START(2) = '1') then

            barrel_shifter_control_i <= conv_std_logic_vector(3,3);

        else

            barrel_shifter_control_i <= (others => '0');

        end if;

    end process;


    -- Register the barrel shifter control number

    process(USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            BARREL_SHIFTER_CONTROL_Buffer <= barrel_shifter_control_i after DLY;

        end if;

    end process;

end RTL;
