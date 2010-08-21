--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: chbond_count_dec.vhd,v $
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
--  CHBOND_COUNT_DEC
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: This module decodes the MGT's RXCLKCORCNT.  Its
--               CHANNEL_BOND_LOAD output is active when RXCLKCORCNT
--               indicates the elastic buffer has executed channel
--               bonding for the current RXDATA.
--
--               * Supports Virtex 2 Pro
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use WORK.AURORA.all;
library aurora_2byte;

entity CHBOND_COUNT_DEC is

    port (

            RX_CLK_COR_CNT    : in std_logic_vector(2 downto 0);
            CHANNEL_BOND_LOAD : out std_logic;
            USER_CLK          : in std_logic

         );

end CHBOND_COUNT_DEC;

architecture RTL of CHBOND_COUNT_DEC is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

    constant CHANNEL_BOND_LOAD_CODE : std_logic_vector(2 downto 0) := "101";    -- Code indicating channel bond load complete

-- External Register Declarations --

    signal CHANNEL_BOND_LOAD_Buffer : std_logic;

begin

    CHANNEL_BOND_LOAD <= CHANNEL_BOND_LOAD_Buffer;

-- Main Body of Code --

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            CHANNEL_BOND_LOAD_Buffer <= std_bool(RX_CLK_COR_CNT = CHANNEL_BOND_LOAD_CODE);

        end if;

    end process;

end RTL;
