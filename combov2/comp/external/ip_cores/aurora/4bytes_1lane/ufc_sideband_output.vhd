--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: ufc_sideband_output.vhd,v $
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
--  UFC_SIDEBAND_OUTPUT
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: B. Woodard, N. Gulstone
--
--  Description: UFC_SIDEBAND_OUTPUT generates the UFC_SRC_RDY_N, UFC_EOF_N,
--               UFC_SOF_N and UFC_REM signals for the RX localLink interface.
--
--               This module supports 2 4-byte lane designs.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use WORK.AURORA.all;
library aurora_4byte1lane;

entity UFC_SIDEBAND_OUTPUT is

    port (

            BARREL_SHIFTED_COUNT : in std_logic_vector(0 to 1);
            UFC_STORAGE_COUNT    : in std_logic_vector(0 to 1);
            UFC_START            : in std_logic;
            UFC_SRC_RDY_N        : out std_logic;
            UFC_SOF_N            : out std_logic;
            UFC_EOF_N            : out std_logic;
            UFC_REM              : out std_logic_vector(0 to 1);
            USER_CLK             : in std_logic;
            RESET                : in std_logic

         );

end UFC_SIDEBAND_OUTPUT;

architecture RTL of UFC_SIDEBAND_OUTPUT is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal UFC_SRC_RDY_N_Buffer : std_logic;
    signal UFC_SOF_N_Buffer     : std_logic;
    signal UFC_EOF_N_Buffer     : std_logic;
    signal UFC_REM_Buffer       : std_logic_vector(0 to 1);

-- Internal Register Declarations --

    signal  ufc_sof_early_r    : std_logic;

-- Wire Declarations --

    signal  sum_c                  : std_logic_vector(0 to 2);
    signal  storage_count_2x_c     : std_logic_vector(0 to 2);
    signal  sum_2x_c               : std_logic_vector(0 to 2);
    signal  back_to_back_rem_c     : std_logic_vector(0 to 2);
    signal  non_back_to_back_rem_c : std_logic_vector(0 to 2);
    signal  storage_empty_c        : std_logic;
    signal  message_finished_c     : std_logic;
    signal  back_to_back_ufc_c     : std_logic;

begin

    UFC_SRC_RDY_N <= UFC_SRC_RDY_N_Buffer;
    UFC_SOF_N     <= UFC_SOF_N_Buffer;
    UFC_EOF_N     <= UFC_EOF_N_Buffer;
    UFC_REM       <= UFC_REM_Buffer;

-- Main Body of Code --

    -- Calculate the output --

    -- Assert ufc_src_rdy_n whenever data is moved to the output.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (RESET = '1') then

                UFC_SRC_RDY_N_Buffer <= '1' after DLY;

            else

                UFC_SRC_RDY_N_Buffer <= not std_bool(UFC_STORAGE_COUNT > conv_std_logic_vector(0,2)) after DLY;

            end if;

        end if;

    end process;


    -- Assert ufc_sof one cycle after a new frame is delivered to storage.

    process(USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            ufc_sof_early_r <= UFC_START after DLY;

            UFC_SOF_N_Buffer <= not ufc_sof_early_r after DLY;

        end if;

    end process;


    sum_c <= conv_std_logic_vector(0,3) + UFC_STORAGE_COUNT + BARREL_SHIFTED_COUNT;


    -- Detect empty storage.

    storage_empty_c <= std_bool(not (UFC_STORAGE_COUNT > conv_std_logic_vector(0,2)));


    -- Detect back to back ufc messages.

    back_to_back_ufc_c <= not storage_empty_c and UFC_START;


    -- Detect messages that are finishing.

    message_finished_c <= not storage_empty_c and (std_bool(sum_c <= conv_std_logic_vector(2,3)) or UFC_START);


    -- Assert eof_n when the storage will empty or a new frame arrives.

    process(USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            UFC_EOF_N_Buffer <= not message_finished_c after DLY;

        end if;

    end process;


    -- REM calculations

    storage_count_2x_c <= UFC_STORAGE_COUNT & '0';

    sum_2x_c <= sum_c(1 to 2) & '0';

    back_to_back_rem_c <= storage_count_2x_c - conv_std_logic_vector(1,3);

    non_back_to_back_rem_c <= sum_2x_c - conv_std_logic_vector(1,3);


    -- Rem depends on the number of valid bytes being transferred to output
    -- on the eof cycle.

    process(USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (back_to_back_ufc_c = '1') then

                UFC_REM_Buffer <= back_to_back_rem_c(1 to 2) after DLY;

            else

                UFC_REM_Buffer <= non_back_to_back_rem_c(1 to 2) after DLY;

            end if;

        end if;

    end process;

end RTL;
