--
--      Project:  Aurora Module Generator version 2.4
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: error_detect_4byte.vhd,v $
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
--  ERROR_DETECT_4BYTE
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description : The ERROR_DETECT module monitors the MGT to detect hard errors.
--                It accumulates the Soft errors according to the leaky bucket
--                algorithm described in the Aurora Specification to detect Hard
--                errors.  All errors are reported to the Global Logic Interface.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use WORK.AURORA.all;

entity ERROR_DETECT_4BYTE is

    port (

    -- Lane Init SM Interface

            ENABLE_ERROR_DETECT : in std_logic;
            HARD_ERROR_RESET    : out std_logic;

    -- Global Logic Interface

            SOFT_ERROR          : out std_logic_vector(0 to 1);
            HARD_ERROR          : out std_logic;

    -- MGT Interface

            RX_DISP_ERR         : in std_logic_vector(3 downto 0);
            TX_K_ERR            : in std_logic_vector(3 downto 0);
            RX_NOT_IN_TABLE     : in std_logic_vector(3 downto 0);
            RX_BUF_STATUS       : in std_logic;
            TX_BUF_ERR          : in std_logic;
            RX_REALIGN          : in std_logic;

    -- System Interface

            USER_CLK            : in std_logic

         );

end ERROR_DETECT_4BYTE;

architecture RTL of ERROR_DETECT_4BYTE is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal HARD_ERROR_RESET_Buffer : std_logic;
    signal SOFT_ERROR_Buffer       : std_logic_vector(0 to 1);
    signal HARD_ERROR_Buffer       : std_logic;

-- Internal Register Declarations --

    signal count_0_r       : std_logic_vector(0 to 1);
    signal count_1_r       : std_logic_vector(0 to 1);
    signal bucket_full_0_r : std_logic;
    signal bucket_full_1_r : std_logic;
    signal soft_error_r    : std_logic_vector(0 to 3);
    signal good_count_0_r  : std_logic_vector(0 to 1);
    signal good_count_1_r  : std_logic_vector(0 to 1);

begin

    HARD_ERROR_RESET <= HARD_ERROR_RESET_Buffer;
    SOFT_ERROR       <= SOFT_ERROR_Buffer;
    HARD_ERROR       <= HARD_ERROR_Buffer;

-- Main Body of Code --

    -- Detect Soft Errors.  The lane is divided into 2 2-byte sublanes for this purpose.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            -- Sublane 0

            soft_error_r(0) <= ENABLE_ERROR_DETECT and (RX_DISP_ERR(3) or RX_NOT_IN_TABLE(3)) after DLY;
            soft_error_r(1) <= ENABLE_ERROR_DETECT and (RX_DISP_ERR(2) or RX_NOT_IN_TABLE(2)) after DLY;

            -- Sublane 1

            soft_error_r(2) <= ENABLE_ERROR_DETECT and (RX_DISP_ERR(1) or RX_NOT_IN_TABLE(1)) after DLY;
            soft_error_r(3) <= ENABLE_ERROR_DETECT and (RX_DISP_ERR(0) or RX_NOT_IN_TABLE(0)) after DLY;

        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            -- Sublane 0

            SOFT_ERROR_Buffer(0) <= soft_error_r(0) or soft_error_r(1) after DLY;

            -- Sublane 1

            SOFT_ERROR_Buffer(1) <= soft_error_r(2) or soft_error_r(3) after DLY;

        end if;

    end process;


    -- Detect Hard Errors

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            HARD_ERROR_Buffer <= ENABLE_ERROR_DETECT and
                                 (std_bool(TX_K_ERR /= "0000") or RX_BUF_STATUS or
                                 TX_BUF_ERR or RX_REALIGN or bucket_full_0_r or bucket_full_1_r) after DLY;

        end if;

    end process;

    -- Assert hard error reset when there is a hard error.  This line of code is
    -- basically just a renaming for the two fanout branches of the hard error
    -- signal.

    HARD_ERROR_RESET_Buffer <= HARD_ERROR_Buffer;


    -- Leaky Bucket Sublane 0 --

    -- Good cycle counter: it takes 2 good cycles in a row to remove a demerit from
    -- the leaky bucket.

    process (USER_CLK)

        variable vec : std_logic_vector(3 downto 0);

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (ENABLE_ERROR_DETECT = '0') then

                good_count_0_r <= "01" after DLY;

            else

                vec := soft_error_r(0 to 1) & good_count_0_r;

                case vec is

                    when "0000" => good_count_0_r <= "01" after DLY;
                    when "0001" => good_count_0_r <= "10" after DLY;
                    when "0010" => good_count_0_r <= "01" after DLY;
                    when "0011" => good_count_0_r <= "01" after DLY;
                    when others => good_count_0_r <= "00" after DLY;

                end case;

            end if;

        end if;

    end process;


    -- Perform the leaky bucket algorithm using an up/down counter.  A drop is
    -- added to the bucket whenever a soft error occurs, and is allowed to leak
    -- out whenever the good cycles counter reaches 2.  Once the bucket fills
    -- (3 drops) it stays full until it is reset by disabling and then enabling
    -- the error detection circuit.

    process (USER_CLK)

        variable vec : std_logic_vector(4 downto 0);

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (ENABLE_ERROR_DETECT = '0') then

                count_0_r <= "00" after DLY;

            else

                vec := soft_error_r(0 to 1) & good_count_0_r(0) & count_0_r;

                case vec is

                    when "00000" => count_0_r <= count_0_r after DLY;
                    when "00001" => count_0_r <= count_0_r after DLY;
                    when "00010" => count_0_r <= count_0_r after DLY;
                    when "00011" => count_0_r <= count_0_r after DLY;

                    when "00100" => count_0_r <= "00" after DLY;
                    when "00101" => count_0_r <= "00" after DLY;
                    when "00110" => count_0_r <= "01" after DLY;
                    when "00111" => count_0_r <= "11" after DLY;

                    when "01000" => count_0_r <= "01" after DLY;
                    when "01001" => count_0_r <= "10" after DLY;
                    when "01010" => count_0_r <= "11" after DLY;
                    when "01011" => count_0_r <= "11" after DLY;

                    when "01100" => count_0_r <= "01" after DLY;
                    when "01101" => count_0_r <= "10" after DLY;
                    when "01110" => count_0_r <= "11" after DLY;
                    when "01111" => count_0_r <= "11" after DLY;

                    when "10000" => count_0_r <= "01" after DLY;
                    when "10001" => count_0_r <= "10" after DLY;
                    when "10010" => count_0_r <= "11" after DLY;
                    when "10011" => count_0_r <= "11" after DLY;

                    when "10100" => count_0_r <= "01" after DLY;
                    when "10101" => count_0_r <= "10" after DLY;
                    when "10110" => count_0_r <= "11" after DLY;
                    when "10111" => count_0_r <= "11" after DLY;

                    when "11000" => count_0_r <= "10" after DLY;
                    when "11001" => count_0_r <= "11" after DLY;
                    when "11010" => count_0_r <= "11" after DLY;
                    when "11011" => count_0_r <= "11" after DLY;

                    when "11100" => count_0_r <= "10" after DLY;
                    when "11101" => count_0_r <= "11" after DLY;
                    when "11110" => count_0_r <= "11" after DLY;
                    when "11111" => count_0_r <= "11" after DLY;

                    when others  => count_0_r <= "XX" after DLY;

                end case;

            end if;

        end if;

    end process;


    -- Detect when the bucket is full and register the signal.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            bucket_full_0_r <= std_bool(count_0_r = "11") after DLY;

        end if;

    end process;


    -- Leaky Bucket Sublane 1 --

    -- Good cycle counter: it takes 2 good cycles in a row to remove a demerit from
    -- the leaky bucket.

    process (USER_CLK)

        variable vec : std_logic_vector(3 downto 0);

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (ENABLE_ERROR_DETECT = '0') then

                good_count_1_r <= "01" after DLY;

            else

                vec := soft_error_r(2 to 3) & good_count_1_r;

                case vec is

                    when "0000" => good_count_1_r <= "01" after DLY;
                    when "0001" => good_count_1_r <= "10" after DLY;
                    when "0010" => good_count_1_r <= "01" after DLY;
                    when "0011" => good_count_1_r <= "01" after DLY;
                    when others => good_count_1_r <= "00" after DLY;

                end case;

            end if;

        end if;

    end process;


    -- Perform the leaky bucket algorithm using an up/down counter.  A drop is
    -- added to the bucket whenever a soft error occurs, and is allowed to leak
    -- out whenever the good cycles counter reaches 2.  Once the bucket fills
    -- (3 drops) it stays full until it is reset by disabling and then enabling
    -- the error detection circuit.

    process (USER_CLK)

        variable vec : std_logic_vector(4 downto 0);

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (ENABLE_ERROR_DETECT = '0') then

                count_1_r <= "00" after DLY;

            else

                vec := soft_error_r(2 to 3) & good_count_1_r(0) & count_1_r;

                case vec is

                    when "00000" => count_1_r <= count_1_r after DLY;
                    when "00001" => count_1_r <= count_1_r after DLY;
                    when "00010" => count_1_r <= count_1_r after DLY;
                    when "00011" => count_1_r <= count_1_r after DLY;

                    when "00100" => count_1_r <= "00" after DLY;
                    when "00101" => count_1_r <= "00" after DLY;
                    when "00110" => count_1_r <= "01" after DLY;
                    when "00111" => count_1_r <= "11" after DLY;

                    when "01000" => count_1_r <= "01" after DLY;
                    when "01001" => count_1_r <= "10" after DLY;
                    when "01010" => count_1_r <= "11" after DLY;
                    when "01011" => count_1_r <= "11" after DLY;

                    when "01100" => count_1_r <= "01" after DLY;
                    when "01101" => count_1_r <= "10" after DLY;
                    when "01110" => count_1_r <= "11" after DLY;
                    when "01111" => count_1_r <= "11" after DLY;

                    when "10000" => count_1_r <= "01" after DLY;
                    when "10001" => count_1_r <= "10" after DLY;
                    when "10010" => count_1_r <= "11" after DLY;
                    when "10011" => count_1_r <= "11" after DLY;

                    when "10100" => count_1_r <= "01" after DLY;
                    when "10101" => count_1_r <= "10" after DLY;
                    when "10110" => count_1_r <= "11" after DLY;
                    when "10111" => count_1_r <= "11" after DLY;

                    when "11000" => count_1_r <= "10" after DLY;
                    when "11001" => count_1_r <= "11" after DLY;
                    when "11010" => count_1_r <= "11" after DLY;
                    when "11011" => count_1_r <= "11" after DLY;

                    when "11100" => count_1_r <= "10" after DLY;
                    when "11101" => count_1_r <= "11" after DLY;
                    when "11110" => count_1_r <= "11" after DLY;
                    when "11111" => count_1_r <= "11" after DLY;

                    when others  => count_1_r <= "XX" after DLY;

                end case;

            end if;

        end if;

    end process;


    -- Detect when the bucket is full and register the signal.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            bucket_full_1_r <= std_bool(count_1_r = "11") after DLY;

        end if;

    end process;

end RTL;
