--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: sideband_output.vhd,v $
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
--  SIDEBAND_OUTPUT
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  Description: SIDEBAND_OUTPUT generates the SRC_RDY_N, EOF_N, SOF_N and
--               RX_REM signals for the RX localLink interface.
--
--               This module supports 4 4-byte lane designs.
--
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;
library aurora_8byte;

entity SIDEBAND_OUTPUT is

    port (

            LEFT_ALIGNED_COUNT : in std_logic_vector(0 to 2);
            STORAGE_COUNT      : in std_logic_vector(0 to 2);
            END_BEFORE_START   : in std_logic;
            END_AFTER_START    : in std_logic;
            START_DETECTED     : in std_logic;
            START_WITH_DATA    : in std_logic;
            PAD                : in std_logic;
            FRAME_ERROR        : in std_logic;
            USER_CLK           : in std_logic;
            RESET              : in std_logic;
            END_STORAGE        : out std_logic;
            SRC_RDY_N          : out std_logic;
            SOF_N              : out std_logic;
            EOF_N              : out std_logic;
            RX_REM             : out std_logic_vector(0 to 2);
            FRAME_ERROR_RESULT : out std_logic

         );

end SIDEBAND_OUTPUT;

architecture RTL of SIDEBAND_OUTPUT is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal END_STORAGE_Buffer        : std_logic;
    signal SRC_RDY_N_Buffer          : std_logic;
    signal SOF_N_Buffer              : std_logic;
    signal EOF_N_Buffer              : std_logic;
    signal RX_REM_Buffer             : std_logic_vector(0 to 2);
    signal FRAME_ERROR_RESULT_Buffer : std_logic;

-- Internal Register Declarations --

    signal start_next_r    : std_logic;
    signal start_storage_r : std_logic;
    signal end_storage_r   : std_logic;
    signal pad_storage_r   : std_logic;
    signal rx_rem_c        : std_logic_vector(0 to 3);

-- Wire Declarations --

    signal word_valid_c        : std_logic;
    signal total_lanes_c       : std_logic_vector(0 to 3);
    signal excess_c            : std_logic;
    signal storage_not_empty_c : std_logic;

begin

    END_STORAGE        <= END_STORAGE_Buffer;
    SRC_RDY_N          <= SRC_RDY_N_Buffer;
    SOF_N              <= SOF_N_Buffer;
    EOF_N              <= EOF_N_Buffer;
    RX_REM             <= RX_REM_Buffer;
    FRAME_ERROR_RESULT <= FRAME_ERROR_RESULT_Buffer;

-- Main Body of Code --

    -- Storage not Empty --

    -- Determine whether there is any data in storage.

    storage_not_empty_c <= std_bool(STORAGE_COUNT /= conv_std_logic_vector(0,3));


    -- Start Next Register --

    -- start_next_r indicates that the Start Storage Register should be set on the next
    -- cycle.  This condition occurs when an old frame ends, filling storage with ending
    -- data, and the SCP for the next cycle arrives on the same cycle.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                start_next_r <= '0' after DLY;

            else

                start_next_r <= (START_DETECTED and
                                not START_WITH_DATA) and
                                not END_AFTER_START after DLY;

            end if;

        end if;

    end process;


    -- Start Storage Register --

    -- Setting the start storage register indicates the data in storage is from
    -- the start of a frame.  The register is cleared when the data in storage is sent
    -- to the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                start_storage_r <= '0' after DLY;

            else

                if ((start_next_r or START_WITH_DATA) = '1') then

                    start_storage_r <= '1' after DLY;

                else

                    if (word_valid_c = '1') then

                        start_storage_r <= '0' after DLY;

                    end if;

                end if;

            end if;

        end if;

    end process;


    -- End Storage Register --

    -- Setting the end storage register indicates the data in storage is from the end
    -- of a frame.  The register is cleared when the data in storage is sent to the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                end_storage_r <= '0' after DLY;

            else

                if ((((END_BEFORE_START and not START_WITH_DATA) and std_bool(total_lanes_c /= "0000")) or
                    (END_AFTER_START and START_WITH_DATA)) = '1') then

                    end_storage_r <= '1' after DLY;

                else

                    end_storage_r <= '0' after DLY;

                end if;

            end if;

        end if;

    end process;


    END_STORAGE_Buffer <=  end_storage_r;


    -- Pad Storage Register --

    -- Setting the pad storage register indicates that the data in storage had a pad
    -- character associated with it.  The register is cleared when the data in storage
    -- is sent to the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                pad_storage_r <= '0' after DLY;

            else

                if (PAD = '1') then

                    pad_storage_r <= '1' after DLY;

                else

                    if (word_valid_c = '1') then

                        pad_storage_r <= '0' after DLY;

                    end if;

                end if;

            end if;

        end if;

    end process;


    -- Word Valid signal and SRC_RDY register --

    -- The word valid signal indicates that the output word has valid data.  This can
    -- only occur when data is removed from storage.  Furthermore, the data must be
    -- marked as valid so that the user knows to read the data as it appears on the
    -- LocalLink interface.

    word_valid_c <= (END_BEFORE_START and START_WITH_DATA) or
                    (excess_c and not START_WITH_DATA) or
                    (end_storage_r);


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if ((RESET or FRAME_ERROR) = '1') then

                SRC_RDY_N_Buffer <= '1' after DLY;

            else

                SRC_RDY_N_Buffer <= not word_valid_c after DLY;

            end if;

        end if;

    end process;


    -- Frame error result signal --
    -- Indicate a frame error whenever the deframer detects a frame error, or whenever
    -- a frame without data is detected.
    -- Empty frames are detected by looking for frames that end while the storage
    -- register is empty. We must be careful not to confuse the data from seperate
    -- frames.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            FRAME_ERROR_RESULT_Buffer <= FRAME_ERROR or

                                         (END_AFTER_START and not START_WITH_DATA) or
                                         (END_BEFORE_START and std_bool(total_lanes_c = "0000") and not START_WITH_DATA) or
                                         (END_BEFORE_START and START_WITH_DATA and not storage_not_empty_c) after DLY;

        end if;

    end process;




    -- The total_lanes and excess signals --

    -- When there is too much data to put into storage, the excess signal is asserted.

    total_lanes_c <= conv_std_logic_vector(0,4) + LEFT_ALIGNED_COUNT + STORAGE_COUNT;

    excess_c <= std_bool(total_lanes_c > conv_std_logic_vector(4,4));


    -- The Start of Frame signal --

    -- To save logic, start of frame is asserted from the time the start of a frame
    -- is placed in storage to the time it is placed on the locallink output register.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            SOF_N_Buffer <= not start_storage_r after DLY;

        end if;

    end process;


    -- The end of frame signal --

    -- End of frame is asserted when storage contains ended data, or when an ECP arrives
    -- at the same time as new data that must replace old data in storage.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            EOF_N_Buffer <= not (end_storage_r or ((END_BEFORE_START and
                START_WITH_DATA) and storage_not_empty_c)) after DLY;

        end if;

    end process;


    -- The RX_REM signal --

    -- RX_REM is equal to the number of bytes written to the output, minus 1 if there is
    -- a pad.

    process (PAD, pad_storage_r, START_WITH_DATA, end_storage_r, STORAGE_COUNT, total_lanes_c)

    begin

        if ((end_storage_r or START_WITH_DATA) = '1') then

            if (pad_storage_r = '1') then

                rx_rem_c <= conv_std_logic_vector(0,4) + ((STORAGE_COUNT & '0') - conv_std_logic_vector(2,4));

            else

                rx_rem_c <= conv_std_logic_vector(0,4) + ((STORAGE_COUNT & '0') - conv_std_logic_vector(1,4));

            end if;


        else

            if ((PAD or pad_storage_r) = '1') then

                rx_rem_c <= (total_lanes_c(1 to 3) & '0') - conv_std_logic_vector(2,4);

            else

                rx_rem_c <= (total_lanes_c(1 to 3) & '0') - conv_std_logic_vector(1,4);

            end if;


        end if;

    end process;


    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            RX_REM_Buffer <= rx_rem_c(1 to 3) after DLY;

        end if;

    end process;

end RTL;
