--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: tx_ll_datapath.vhd,v $
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
--  TX_LL_DATAPATH
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  Description: This module pipelines the data path while handling the PAD
--               character placement and valid data flags.
--
--               This module supports 4 4-byte lane designs
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_8byte;

entity TX_LL_DATAPATH is

    port (

    -- LocalLink PDU Interface

            TX_D         : in std_logic_vector(0 to 63);
            TX_REM       : in std_logic_vector(0 to 2);
            TX_SRC_RDY_N : in std_logic;
            TX_SOF_N     : in std_logic;
            TX_EOF_N     : in std_logic;

    -- Aurora Lane Interface

            TX_PE_DATA_V : out std_logic_vector(0 to 3);
            GEN_PAD      : out std_logic_vector(0 to 3);
            TX_PE_DATA   : out std_logic_vector(0 to 63);

    -- TX_LL Control Module Interface

            HALT_C       : in std_logic;
            TX_DST_RDY_N : in std_logic;
            UFC_MESSAGE  : in std_logic_vector(0 to 3);

    -- System Interface

            CHANNEL_UP   : in std_logic;
            USER_CLK     : in std_logic

         );

end TX_LL_DATAPATH;

architecture RTL of TX_LL_DATAPATH is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal TX_PE_DATA_V_Buffer : std_logic_vector(0 to 3);
    signal GEN_PAD_Buffer      : std_logic_vector(0 to 3);
    signal TX_PE_DATA_Buffer   : std_logic_vector(0 to 63);

-- Internal Register Declarations --

    signal in_frame_r              : std_logic;
    signal storage_r               : std_logic_vector(0 to 15);
    signal storage_v_r             : std_logic;
    signal storage_ufc_v_r         : std_logic;
    signal storage_pad_r           : std_logic;
    signal tx_pe_data_r            : std_logic_vector(0 to 63);
    signal valid_c                 : std_logic_vector(0 to 3);
    signal tx_pe_data_v_r          : std_logic_vector(0 to 3);
    signal tx_pe_ufc_v_r           : std_logic_vector(0 to 3);
    signal gen_pad_c               : std_logic_vector(0 to 3);
    signal gen_pad_r               : std_logic_vector(0 to 3);
    signal tx_d_pipeline_r         : std_logic_vector(0 to 63);
    signal tx_rem_pipeline_r       : std_logic_vector(0 to 2);
    signal tx_src_rdy_n_pipeline_r : std_logic;
    signal tx_sof_n_pipeline_r     : std_logic;
    signal tx_eof_n_pipeline_r     : std_logic;
    signal halt_c_pipeline_r       : std_logic;
    signal tx_dst_rdy_n_pipeline_r : std_logic;
    signal ufc_message_pipeline_r  : std_logic_vector(0 to 3);

-- Internal Wire Declarations --
    
    signal ll_valid_c              : std_logic;
    signal in_frame_c              : std_logic;

begin

    TX_PE_DATA_V <= TX_PE_DATA_V_Buffer;
    GEN_PAD      <= GEN_PAD_Buffer;
    TX_PE_DATA   <= TX_PE_DATA_Buffer;

-- Main Body of Code --

    -- Pipeline all inputs.  This creates 'travelling registers',
    -- which makes it easier for par to place blocks to reduce congestion while
    -- meeting all timing constriants.

    -- First we pipeline the control signals.  Some of these signals are used
    -- many times in the datapath.  The sythesis tool will replicate these
    -- registers to keep fanout low and preserve timing.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if(CHANNEL_UP = '0') then

                tx_src_rdy_n_pipeline_r <= '1' after DLY;
                tx_sof_n_pipeline_r     <= '1' after DLY;
                tx_eof_n_pipeline_r     <= '1' after DLY;
                halt_c_pipeline_r       <= '0' after DLY;
                tx_dst_rdy_n_pipeline_r <= '1' after DLY;
                ufc_message_pipeline_r  <= "0000" after DLY;

            else

                tx_src_rdy_n_pipeline_r <= TX_SRC_RDY_N after DLY;
                tx_sof_n_pipeline_r     <= TX_SOF_N     after DLY;
                tx_eof_n_pipeline_r     <= TX_EOF_N     after DLY;
                halt_c_pipeline_r       <= HALT_C       after DLY;
                tx_dst_rdy_n_pipeline_r <= TX_DST_RDY_N after DLY;
                ufc_message_pipeline_r  <= UFC_MESSAGE  after DLY;

            end if;

        end if;

    end process;


    -- We pipeline the data and REM seperately from the control signals: we
    -- use no reset because the routing is expensive, and the signals are
    -- all qualified by the control signals.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            tx_d_pipeline_r   <= TX_D   after DLY;
            tx_rem_pipeline_r <= TX_REM after DLY;

        end if;

    end process;



    -- LocalLink input is only valid when TX_SRC_RDY_N and TX_DST_RDY_N are both asserted
    ll_valid_c    <=   not tx_src_rdy_n_pipeline_r and not tx_dst_rdy_n_pipeline_r;


    -- Data must only be read if it is within a frame. If a frame will last multiple cycles
    -- we assert in_frame_r as long as the frame is open.
    process(USER_CLK)
    begin
        if(USER_CLK'event and USER_CLK = '1') then
            if(CHANNEL_UP = '0') then
                in_frame_r  <=  '1' after DLY;
            elsif(ll_valid_c = '1') then
                if( (tx_sof_n_pipeline_r = '0') and (tx_eof_n_pipeline_r = '1') ) then
                    in_frame_r  <=  '1' after DLY;
                elsif(tx_eof_n_pipeline_r = '0') then
                    in_frame_r  <=  '0' after DLY;
                end if;
            end if;
        end if;
    end process;
    
        
    in_frame_c   <=   ll_valid_c and (in_frame_r  or not tx_sof_n_pipeline_r);






    -- The last 2 bytes of data from the LocalLink interface must be stored
    -- for the next cycle to make room for the SCP character that must be
    -- placed at the beginning of the lane.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                storage_r <= tx_d_pipeline_r(48 to 63) after DLY;

            end if;

        end if;

    end process;


    -- All of the remaining bytes (except the last two) must be shifted
    -- and registered to be sent to the Channel.  The stored bytes go
    -- into the first position.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                tx_pe_data_r <= storage_r & tx_d_pipeline_r(0 to 47) after DLY;

            end if;

        end if;

    end process;


    -- We generate the valid_c signal based on the REM signal and the EOF signal.

    process (tx_eof_n_pipeline_r, tx_rem_pipeline_r)

    begin

        if (tx_eof_n_pipeline_r = '1') then

            valid_c <= "1111";

        else

            case tx_rem_pipeline_r(0 to 2) is

                when "000" => valid_c <= "1000";
                when "001" => valid_c <= "1000";
                when "010" => valid_c <= "1100";
                when "011" => valid_c <= "1100";
                when "100" => valid_c <= "1110";
                when "101" => valid_c <= "1110";
                when "110" => valid_c <= "1111";
                when "111" => valid_c <= "1111";
                when others => valid_c <= "1111";

            end case;

        end if;

    end process;


    -- If the last 2 bytes in the word are valid, they are placed in the storage register and
    -- storage_v_r is asserted to indicate the data is valid.  Note that data is only moved to
    -- storage if the PDU datapath is not halted, the data is valid and both TX_SRC_RDY_N
    -- and TX_DST_RDY_N (as indicated by DATA_VALID) are asserted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                storage_v_r <= valid_c(3)  and in_frame_c after DLY;

            end if;

        end if;

    end process;


    -- The storage_ufc_v_r register is asserted when valid UFC data is placed in the storage register.
    -- Note that UFC data cannot be halted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            storage_ufc_v_r <= ufc_message_pipeline_r(3) after DLY;

        end if;

    end process;


    -- The tx_pe_data_v_r registers track valid data in the TX_PE_DATA register.  The data is valid
    -- if it was valid in the previous stage.  Since the first 2 bytes come from storage, validity is
    -- determined from the storage_v_r signal.  The remaining bytes are valid if their valid signal
    -- is asserted, and both TX_SRC_RDY_N and TX_DST_RDY_N (as indicated by DATA_VALID) are asserted.
    -- Note that pdu data movement can be frozen by the halt signal.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                tx_pe_data_v_r(0) <= storage_v_r after DLY;

                tx_pe_data_v_r(1) <= valid_c(0) and in_frame_c after DLY;

                tx_pe_data_v_r(2) <= valid_c(1) and in_frame_c after DLY;

                tx_pe_data_v_r(3) <= valid_c(2) and in_frame_c after DLY;

            end if;

        end if;

    end process;


    -- The tx_pe_ufc_v_r register tracks valid UFC data in the TX_PE_DATA register.  The first 2 bytes
    -- come from storage: they are valid if storage_ufc_v_r was asserted.  The remaining bytes come from
    -- the TX_D input.  They are valid if UFC_MESSAGE was high when they were sampled.  Note that UFC data
    -- cannot be halted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            tx_pe_ufc_v_r(0) <= storage_ufc_v_r after DLY;
            tx_pe_ufc_v_r(1) <= ufc_message_pipeline_r(0) after DLY;
            tx_pe_ufc_v_r(2) <= ufc_message_pipeline_r(1) after DLY;
            tx_pe_ufc_v_r(3) <= ufc_message_pipeline_r(2) after DLY;

        end if;

    end process;


    -- We generate the gen_pad_c signal based on the REM signal and the EOF signal.

    process (tx_eof_n_pipeline_r, tx_rem_pipeline_r)

    begin

        if (tx_eof_n_pipeline_r = '1') then

            gen_pad_c <= "0000";

        else

            case tx_rem_pipeline_r(0 to 2) is

                when "000" => gen_pad_c <= "1000";
                when "001" => gen_pad_c <= "0000";
                when "010" => gen_pad_c <= "0100";
                when "011" => gen_pad_c <= "0000";
                when "100" => gen_pad_c <= "0010";
                when "101" => gen_pad_c <= "0000";
                when "110" => gen_pad_c <= "0001";
                when "111" => gen_pad_c <= "0000";
                when others => gen_pad_c <= "0000";

            end case;

        end if;

    end process;


    -- Store a padded byte pair if it's padded, TX_SRC_RDY_N is asserted, and data is valid.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                storage_pad_r <= gen_pad_c(3) and in_frame_c after DLY;

            end if;

        end if;

    end process;


    -- Register the gen_pad_r signals.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (halt_c_pipeline_r = '0') then

                gen_pad_r(0) <= storage_pad_r after DLY;

                gen_pad_r(1) <= gen_pad_c(0) and in_frame_c after DLY;

                gen_pad_r(2) <= gen_pad_c(1) and in_frame_c after DLY;

                gen_pad_r(3) <= gen_pad_c(2) and in_frame_c after DLY;

            end if;

        end if;

    end process;


    -- Implement the data out register.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            TX_PE_DATA_Buffer      <= tx_pe_data_r after DLY;
            TX_PE_DATA_V_Buffer(0) <= (tx_pe_data_v_r(0) and not halt_c_pipeline_r) or tx_pe_ufc_v_r(0) after DLY;
            TX_PE_DATA_V_Buffer(1) <= (tx_pe_data_v_r(1) and not halt_c_pipeline_r) or tx_pe_ufc_v_r(1) after DLY;
            TX_PE_DATA_V_Buffer(2) <= (tx_pe_data_v_r(2) and not halt_c_pipeline_r) or tx_pe_ufc_v_r(2) after DLY;
            TX_PE_DATA_V_Buffer(3) <= (tx_pe_data_v_r(3) and not halt_c_pipeline_r) or tx_pe_ufc_v_r(3) after DLY;
            GEN_PAD_Buffer(0)      <= (gen_pad_r(0) and not halt_c_pipeline_r) and not tx_pe_ufc_v_r(0) after DLY;
            GEN_PAD_Buffer(1)      <= (gen_pad_r(1) and not halt_c_pipeline_r) and not tx_pe_ufc_v_r(1) after DLY;
            GEN_PAD_Buffer(2)      <= (gen_pad_r(2) and not halt_c_pipeline_r) and not tx_pe_ufc_v_r(2) after DLY;
            GEN_PAD_Buffer(3)      <= (gen_pad_r(3) and not halt_c_pipeline_r) and not tx_pe_ufc_v_r(3) after DLY;

        end if;

    end process;


end RTL;
