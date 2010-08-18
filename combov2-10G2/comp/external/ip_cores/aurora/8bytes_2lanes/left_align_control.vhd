--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: left_align_control.vhd,v $
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
--  LEFT_ALIGN_CONTROL
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: The LEFT_ALIGN_CONTROL is used to control the Left Align Muxes in
--               the RX_LL module.  Each module supports up to 8 lanes.  Modules can
--               be combined in stages to support channels with more than 8 lanes.
--
--               This module supports 4 4-byte lane designs.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
library aurora_8byte;

entity LEFT_ALIGN_CONTROL is

    port (

            PREVIOUS_STAGE_VALID : in std_logic_vector(0 to 3);
            MUX_SELECT           : out std_logic_vector(0 to 11);
            VALID                : out std_logic_vector(0 to 3);
            USER_CLK             : in std_logic;
            RESET                : in std_logic

         );

end LEFT_ALIGN_CONTROL;

architecture RTL of LEFT_ALIGN_CONTROL is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal MUX_SELECT_Buffer : std_logic_vector(0 to 11);
    signal VALID_Buffer      : std_logic_vector(0 to 3);

-- Internal Register Declarations --

    signal  mux_select_c : std_logic_vector(0 to 11);
    signal  valid_c      : std_logic_vector(0 to 3);

begin

    MUX_SELECT <= MUX_SELECT_Buffer;
    VALID      <= VALID_Buffer;

-- Main Body of Code --

    -- SELECT --

    -- Lane 0

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0001" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(3,3);

            when "0010" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(2,3);

            when "0011" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(2,3);

            when "0100" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(1,3);

            when "0101" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(1,3);

            when "0110" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(1,3);

            when "0111" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(1,3);

            when "1000" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1001" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1010" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1011" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1100" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1101" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1110" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when "1111" =>

                mux_select_c(0 to 2) <= conv_std_logic_vector(0,3);

            when others =>

                mux_select_c(0 to 2) <= (others => 'X');

        end case;

    end process;


    -- Lane 1

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0011" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(2,3);

            when "0101" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(2,3);

            when "0110" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(1,3);

            when "0111" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(1,3);

            when "1001" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(2,3);

            when "1010" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(1,3);

            when "1011" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(1,3);

            when "1100" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(0,3);

            when "1101" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(0,3);

            when "1110" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(0,3);

            when "1111" =>

                mux_select_c(3 to 5) <= conv_std_logic_vector(0,3);

            when others =>

                mux_select_c(3 to 5) <= (others => 'X');

        end case;

    end process;


    -- Lane 2

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0111" =>

                mux_select_c(6 to 8) <= conv_std_logic_vector(1,3);

            when "1011" =>

                mux_select_c(6 to 8) <= conv_std_logic_vector(1,3);

            when "1101" =>

                mux_select_c(6 to 8) <= conv_std_logic_vector(1,3);

            when "1110" =>

                mux_select_c(6 to 8) <= conv_std_logic_vector(0,3);

            when "1111" =>

                mux_select_c(6 to 8) <= conv_std_logic_vector(0,3);

            when others =>

                mux_select_c(6 to 8) <= (others => 'X');

        end case;

    end process;


    -- Lane 3

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "1111" =>

                mux_select_c(9 to 11) <= conv_std_logic_vector(0,3);

            when others =>

                mux_select_c(9 to 11) <= (others => 'X');

        end case;

    end process;


    -- Register the select signals.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            MUX_SELECT_Buffer <= mux_select_c after DLY;

        end if;

    end process;


    -- VALID --

    -- Lane 0

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0001" =>

                valid_c(0) <= '1';

            when "0010" =>

                valid_c(0) <= '1';

            when "0011" =>

                valid_c(0) <= '1';

            when "0100" =>

                valid_c(0) <= '1';

            when "0101" =>

                valid_c(0) <= '1';

            when "0110" =>

                valid_c(0) <= '1';

            when "0111" =>

                valid_c(0) <= '1';

            when "1000" =>

                valid_c(0) <= '1';

            when "1001" =>

                valid_c(0) <= '1';

            when "1010" =>

                valid_c(0) <= '1';

            when "1011" =>

                valid_c(0) <= '1';

            when "1100" =>

                valid_c(0) <= '1';

            when "1101" =>

                valid_c(0) <= '1';

            when "1110" =>

                valid_c(0) <= '1';

            when "1111" =>

                valid_c(0) <= '1';

            when others =>

                valid_c(0) <= '0';

        end case;

    end process;


    -- Lane 1

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0011" =>

                valid_c(1) <= '1';

            when "0101" =>

                valid_c(1) <= '1';

            when "0110" =>

                valid_c(1) <= '1';

            when "0111" =>

                valid_c(1) <= '1';

            when "1001" =>

                valid_c(1) <= '1';

            when "1010" =>

                valid_c(1) <= '1';

            when "1011" =>

                valid_c(1) <= '1';

            when "1100" =>

                valid_c(1) <= '1';

            when "1101" =>

                valid_c(1) <= '1';

            when "1110" =>

                valid_c(1) <= '1';

            when "1111" =>

                valid_c(1) <= '1';

            when others =>

                valid_c(1) <= '0';

        end case;

    end process;


    -- Lane 2

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "0111" =>

                valid_c(2) <= '1';

            when "1011" =>

                valid_c(2) <= '1';

            when "1101" =>

                valid_c(2) <= '1';

            when "1110" =>

                valid_c(2) <= '1';

            when "1111" =>

                valid_c(2) <= '1';

            when others =>

                valid_c(2) <= '0';

        end case;

    end process;


    -- Lane 3

    process (PREVIOUS_STAGE_VALID(0 to 3))

    begin

        case PREVIOUS_STAGE_VALID(0 to 3) is

            when "1111" =>

                valid_c(3) <= '1';

            when others =>

                valid_c(3) <= '0';

        end case;

    end process;


    -- Register the valid signals for the next stage.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                VALID_Buffer <= (others => '0') after DLY;

            else

                VALID_Buffer <= valid_c after DLY;

            end if;

        end if;

    end process;

end RTL;
