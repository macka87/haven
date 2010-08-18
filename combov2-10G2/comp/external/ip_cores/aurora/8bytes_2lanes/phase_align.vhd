--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: phase_align.vhd,v $
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
--  PHASE_ALIGN
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: Phase alignment circuit for the comma alignment signal.  Ensures
--               that the enable comma align signal is syncronous with the MGT
--               recovered clock.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_8byte;

entity PHASE_ALIGN is

    port (

        -- Aurora Lane Interface

            ENA_COMMA_ALIGN : in std_logic;

        -- MGT Interface

            RX_REC_CLK      : in std_logic;
            ENA_CALIGN_REC  : out std_logic

         );

end PHASE_ALIGN;

architecture RTL of PHASE_ALIGN is

-- Attribute Declaration
attribute KEEP_HIERARCHY : string;
attribute KEEP_HIERARCHY of RTL: architecture is "true";



-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal ENA_CALIGN_REC_Buffer : std_logic;

-- Internal Register Declarations --

    signal phase_align_flops_r : std_logic_vector(0 to 1);

begin

    ENA_CALIGN_REC <= ENA_CALIGN_REC_Buffer;

-- Main Body of Code --

    -- To phase align the signal, we sample it using a flop clocked with the recovered
    -- clock.  We then sample the output of the first flop and pass it to the output.
    -- This ensures that the signal is not metastable, and prevents transitions from
    -- occuring except at the clock edge.  The comma alignment circuit cannot tolerate
    -- transitions except at the recovered clock edge.

    process (RX_REC_CLK)

    begin

        if (RX_REC_CLK 'event and RX_REC_CLK = '1') then

            phase_align_flops_r(0) <= ENA_COMMA_ALIGN after DLY;
            phase_align_flops_r(1) <= phase_align_flops_r(0) after DLY;

        end if;

    end process;

    ENA_CALIGN_REC_Buffer <= phase_align_flops_r(1);

end RTL;
