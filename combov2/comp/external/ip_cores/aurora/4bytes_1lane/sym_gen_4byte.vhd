--
--      Project:  Aurora Module Generator version 2.5
--
--         Date:  $Date$
--          Tag:  $Name:  $
--         File:  $RCSfile: sym_gen_4byte.vhd,v $
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
--  SYM_GEN_4BYTE
--
--  Author: Nigel Gulstone
--          Xilinx - Embedded Networking System Engineering Group
--
--  VHDL Translation: Brian Woodard
--                    Xilinx - Garden Valley Design Team
--
--  Description: The SYM_GEN module is a symbol generator for 4-byte Aurora Lanes.
--               Its inputs request the transmission of specific symbols, and its
--               outputs drive the MGT interface to fulfill those requests.
--
--               All generation request inputs must be asserted exclusively
--               except for the GEN_K, GEN_R and GEN_A signals from the Global
--               Logic, and the GEN_PAD and TX_PE_DATA_V signals from TX_LL.
--
--               GEN_K, GEN_R and GEN_A can be asserted anytime, but they are
--               ignored when other signals are being asserted.  This allows the
--               idle generator in the Global Logic to run continuously without
--               feedback, but requires the TX_LL and Lane Init SM modules to
--               be quiescent during Channel Bonding and Verification.
--
--               The GEN_PAD signal is only valid while the TX_PE_DATA_V signal
--               is asserted.  This allows padding to be specified for the LSB
--               of the data transmission.  GEN_PAD must not be asserted when
--               TX_PE_DATA_V is not asserted - this will generate errors.
--
--               This module supports Immediate Mode Native Flow Control.
--
--               This module supports User Flow Control.
--

library IEEE;
use IEEE.STD_LOGIC_1164.all;
library aurora_4byte1lane;

entity SYM_GEN_4BYTE is

    port (

    -- TX_LL Interface                                        -- See description for info about GEN_PAD and TX_PE_DATA_V.

            GEN_SCP      : in std_logic_vector(0 to 1);       -- Generate SCP.
            GEN_ECP      : in std_logic_vector(0 to 1);       -- Generate ECP.
            GEN_SNF      : in std_logic_vector(0 to 1);       -- Generate SNF using code given by FC_NB.
            GEN_SUF      : in std_logic_vector(0 to 1);       -- Generate SUF using code given by FC_NB.
            GEN_PAD      : in std_logic_vector(0 to 1);       -- Replace LSB with Pad character.
            FC_NB        : in std_logic_vector(0 to 7);       -- Size code for Flow Control messages.
            TX_PE_DATA   : in std_logic_vector(0 to 31);      -- Data.  Transmitted when TX_PE_DATA_V is asserted.
            TX_PE_DATA_V : in std_logic_vector(0 to 1);       -- Transmit data.
            GEN_CC       : in std_logic;                      -- Generate Clock Correction symbols.

    -- Global Logic Interface                                 -- See description for info about GEN_K,GEN_R and GEN_A.

            GEN_A        : in std_logic;                      -- Generate A character for MSBYTE
            GEN_K        : in std_logic_vector(0 to 3);       -- Generate K character for selected bytes.
            GEN_R        : in std_logic_vector(0 to 3);       -- Generate R character for selected bytes.
            GEN_V        : in std_logic_vector(0 to 3);       -- Generate Ver data character on selected bytes.

    -- Lane Init SM Interface

            GEN_SP       : in std_logic;                      -- Generate SP pattern.
            GEN_SPA      : in std_logic;                      -- Generate SPA pattern.

    -- MGT Interface

            TX_CHAR_IS_K : out std_logic_vector(3 downto 0);  -- Transmit TX_DATA as a control character.
            TX_DATA      : out std_logic_vector(31 downto 0); -- Data to MGT for transmission to channel partner.

    -- System Interface

            USER_CLK     : in std_logic                       -- Clock for all non-MGT Aurora Logic.

         );

end SYM_GEN_4BYTE;

architecture RTL of SYM_GEN_4BYTE is

-- Parameter Declarations --

    constant DLY : time := 1 ns;

-- External Register Declarations --

    signal TX_CHAR_IS_K_Buffer : std_logic_vector(3 downto 0);
    signal TX_DATA_Buffer      : std_logic_vector(31 downto 0);

-- Internal Register Declarations --

    -- Slack registers.  These registers allow slack for routing delay and automatic retiming.

    signal gen_scp_r      : std_logic_vector(0 to 1);
    signal gen_ecp_r      : std_logic_vector(0 to 1);
    signal gen_snf_r      : std_logic_vector(0 to 1);
    signal gen_suf_r      : std_logic_vector(0 to 1);
    signal gen_pad_r      : std_logic_vector(0 to 1);
    signal fc_nb_r        : std_logic_vector(0 to 7);
    signal tx_pe_data_r   : std_logic_vector(0 to 31);
    signal tx_pe_data_v_r : std_logic_vector(0 to 1);
    signal gen_cc_r       : std_logic;
    signal gen_a_r        : std_logic;
    signal gen_k_r        : std_logic_vector(0 to 3);
    signal gen_r_r        : std_logic_vector(0 to 3);
    signal gen_v_r        : std_logic_vector(0 to 3);
    signal gen_sp_r       : std_logic;
    signal gen_spa_r      : std_logic;

-- Wire Declarations --

    signal idle_c         : std_logic_vector(0 to 3);

begin

    TX_CHAR_IS_K <= TX_CHAR_IS_K_Buffer;
    TX_DATA      <= TX_DATA_Buffer;

-- Main Body of Code --

    -- Register all inputs with the slack registers.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            gen_scp_r      <= GEN_SCP      after DLY;
            gen_ecp_r      <= GEN_ECP      after DLY;
            gen_snf_r      <= GEN_SNF      after DLY;
            gen_suf_r      <= GEN_SUF      after DLY;
            gen_pad_r      <= GEN_PAD      after DLY;
            fc_nb_r        <= FC_NB        after DLY;
            tx_pe_data_r   <= TX_PE_DATA   after DLY;
            tx_pe_data_v_r <= TX_PE_DATA_V after DLY;
            gen_cc_r       <= GEN_CC       after DLY;
            gen_a_r        <= GEN_A        after DLY;
            gen_k_r        <= GEN_K        after DLY;
            gen_r_r        <= GEN_R        after DLY;
            gen_v_r        <= GEN_V        after DLY;
            gen_sp_r       <= GEN_SP       after DLY;
            gen_spa_r      <= GEN_SPA      after DLY;

        end if;

    end process;


    -- Byte 0 --

    -- When none of the byte0 non_idle inputs are asserted, allow idle characters.

    idle_c(0) <= not (gen_scp_r(0)      or
                      gen_ecp_r(0)      or
                      gen_snf_r(0)      or
                      gen_suf_r(0)      or
                      tx_pe_data_v_r(0) or
                      gen_cc_r          or
                      gen_sp_r          or
                      gen_spa_r         or
                      gen_v_r(0));



    -- Generate data for byte0.  Note that all inputs must be asserted exclusively, except
    -- for the GEN_A, GEN_K and GEN_R inputs which are ignored when other characters
    -- are asserted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (gen_scp_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"5C" after DLY;                -- K28.2(SCP)

            end if;

            if (gen_ecp_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"FD" after DLY;                -- K29.7(ECP)

            end if;

            if (gen_snf_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"DC" after DLY;                -- K28.6(SNF)

            end if;

            if (gen_suf_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"9C" after DLY;                -- K28.4(SUF)

            end if;

            if (tx_pe_data_v_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= tx_pe_data_r(0 to 7) after DLY; -- DATA

            end if;

            if (gen_cc_r = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"F7" after DLY;                -- K23.7(CC)

            end if;

            if ((idle_c(0) and gen_a_r) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"7C" after DLY;                -- K28.3(A)

            end if;

            if ((idle_c(0) and gen_k_r(0)) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"BC" after DLY;                -- K28.5(K)

            end if;

            if ((idle_c(0) and gen_r_r(0)) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"1C" after DLY;                -- K28.0(R)

            end if;

            if (gen_sp_r = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"BC" after DLY;                -- K28.5(K)

            end if;

            if (gen_spa_r = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"BC" after DLY;                -- K28.5(K)

            end if;

            if (gen_v_r(0) = '1') then

                TX_DATA_Buffer(31 downto 24) <= X"E8" after DLY;                -- D8.7(Ver data)

            end if;

        end if;

    end process;


    -- Generate control signal for MSB.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            TX_CHAR_IS_K_Buffer(3) <= not (tx_pe_data_v_r(0) or
                                           gen_v_r(0)) after DLY;

        end if;

    end process;


    -- Byte 1 --

    -- When none of the byte1 non_idle inputs are asserted, allow idle characters.  Note
    -- that because gen_pad is only valid with the data valid signal, we only look at
    -- the data valid signal.

    idle_c(1) <= not (gen_scp_r(0)      or
                      gen_ecp_r(0)      or
                      gen_snf_r(0)      or
                      gen_suf_r(0)      or
                      tx_pe_data_v_r(0) or
                      gen_cc_r          or
                      gen_sp_r          or
                      gen_spa_r         or
                      gen_v_r(1));


    -- Generate data for byte1.  Note that all inputs must be asserted exclusively except
    -- for the GEN_PAD signal and the GEN_K and GEN_R set.  GEN_PAD can be asserted
    -- at the same time as TX_DATA_VALID.  This will override TX_DATA valid and replace
    -- the lsb user data with a PAD character.  The GEN_K and GEN_R inputs are
    -- ignored if any other input is asserted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (gen_scp_r(0) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"FB" after DLY;                        -- K27.7(SCP)

            end if;

            if (gen_ecp_r(0) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"FE" after DLY;                        -- K30.7(ECP)

            end if;

            if (gen_snf_r(0) = '1') then

                TX_DATA_Buffer(23 downto 16) <= fc_nb_r(0 to 3) & "0000" after DLY;     -- SNF Data

            end if;

            if (gen_suf_r(0) = '1') then

                TX_DATA_Buffer(23 downto 16) <= fc_nb_r(0 to 3) & "0000" after DLY;     -- SUF Data

            end if;

            if ((tx_pe_data_v_r(0) and gen_pad_r(0)) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"9C" after DLY;                        -- K28.4(PAD)

            end if;

            if ((tx_pe_data_v_r(0) and not gen_pad_r(0)) = '1') then

                TX_DATA_Buffer(23 downto 16) <= tx_pe_data_r(8 to 15) after DLY;        -- DATA

            end if;

            if (gen_cc_r = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"F7" after DLY;                        -- K23.7(CC)

            end if;

            if ((idle_c(1) and gen_k_r(1)) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"BC" after DLY;                        -- K28.5(K)

            end if;

            if ((idle_c(1) and gen_r_r(1)) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"1C" after DLY;                        -- K28.0(R)

            end if;

            if (gen_sp_r = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"4A" after DLY;                        -- D10.2(SP data)

            end if;

            if (gen_spa_r = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"2C" after DLY;                        -- D12.1(SPA data)

            end if;

            if (gen_v_r(1) = '1') then

                TX_DATA_Buffer(23 downto 16) <= X"E8" after DLY;                        -- D8.7(Ver data)

            end if;

        end if;

    end process;


    -- Generate control signal for byte1.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            TX_CHAR_IS_K_Buffer(2) <= not ((tx_pe_data_v_r(0) and not gen_pad_r(0)) or
                                            gen_snf_r(0)      or
                                            gen_suf_r(0)      or
                                            gen_sp_r          or
                                            gen_spa_r         or
                                            gen_v_r(1)) after DLY;

        end if;

    end process;


    -- Byte 2 --

    -- When none of the byte2 non_idle inputs are asserted, allow idle characters.

    idle_c(2) <= not (gen_scp_r(1)      or
                      gen_ecp_r(1)      or
                      gen_snf_r(1)      or
                      gen_suf_r(1)      or
                      tx_pe_data_v_r(1) or
                      gen_cc_r          or
                      gen_sp_r          or
                      gen_spa_r         or
                      gen_v_r(2));



    -- Generate data for byte2.  Note that all inputs must be asserted exclusively,
    -- except for the GEN_K and GEN_R inputs which are ignored when other
    -- characters are asserted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (gen_scp_r(1) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"5C" after DLY;                  -- K28.2(SCP)

            end if;

            if (gen_ecp_r(1) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"FD" after DLY;                  -- K29.7(ECP)

            end if;

            if (gen_snf_r(1) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"DC" after DLY;                  -- K28.6(SNF)

            end if;

            if (gen_suf_r(1) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"9C" after DLY;                  -- K28.4(SUF)

            end if;

            if (tx_pe_data_v_r(1) = '1') then

                TX_DATA_Buffer(15 downto 8) <= tx_pe_data_r(16 to 23) after DLY; -- DATA

            end if;

            if (gen_cc_r = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"F7" after DLY;                  -- K23.7(CC)

            end if;

            if ((idle_c(2) and gen_k_r(2)) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"BC" after DLY;                  -- K28.5(K)

            end if;

            if ((idle_c(2) and gen_r_r(2)) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"1C" after DLY;                  -- K28.0(R)

            end if;

            if (gen_sp_r = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"4A" after DLY;                  -- D10.2(SP data)

            end if;

            if (gen_spa_r = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"2C" after DLY;                  -- D12.1(SPA data)

            end if;

            if (gen_v_r(2) = '1') then

                TX_DATA_Buffer(15 downto 8) <= X"E8" after DLY;                  -- D8.7(Ver data)

            end if;

        end if;

    end process;


    -- Generate control signal for MSB.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            TX_CHAR_IS_K_Buffer(1) <= not (tx_pe_data_v_r(1) or
                                           gen_sp_r          or
                                           gen_spa_r         or
                                           gen_v_r(2)) after DLY;

        end if;

    end process;


    -- Byte 3 --

    -- When none of the byte3 non_idle inputs are asserted, allow idle characters.
    -- Note that because gen_pad is only valid with the data valid signal, we only
    -- look at the data valid signal.

    idle_c(3) <= not (gen_scp_r(1)      or
                      gen_ecp_r(1)      or
                      gen_snf_r(1)      or
                      gen_suf_r(1)      or
                      tx_pe_data_v_r(1) or
                      gen_cc_r          or
                      gen_sp_r          or
                      gen_spa_r         or
                      gen_v_r(3));



    -- Generate data for byte3.  Note that all inputs must be asserted exclusively
    -- except for the GEN_PAD signal and the GEN_K and GEN_R set.  GEN_PAD
    -- can be asserted at the same time as TX_DATA_VALID.  This will override
    -- TX_DATA valid and replace the lsb user data with a PAD character.  The GEN_K
    -- and GEN_R inputs are ignored if any other input is asserted.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            if (gen_scp_r(1) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"FB" after DLY;                    -- K27.7(SCP)

            end if;

            if (gen_ecp_r(1) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"FE" after DLY;                    -- K30.7(ECP)

            end if;

            if (gen_snf_r(1) = '1') then

                TX_DATA_Buffer(7 downto 0) <= fc_nb_r(4 to 7) & "0000" after DLY; -- SNF Data

            end if;

            if (gen_suf_r(1) = '1') then

                TX_DATA_Buffer(7 downto 0) <= fc_nb_r(4 to 7) & "0000" after DLY; -- SUF Data

            end if;

            if ((tx_pe_data_v_r(1) and gen_pad_r(1)) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"9C" after DLY;                    -- K28.4(PAD)

            end if;

            if ((tx_pe_data_v_r(1) and not gen_pad_r(1)) = '1') then

                TX_DATA_Buffer(7 downto 0) <= tx_pe_data_r(24 to 31) after DLY;   -- DATA

            end if;

            if (gen_cc_r = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"F7" after DLY;                    -- K23.7(CC)

            end if;

            if ((idle_c(3) and gen_k_r(3)) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"BC" after DLY;                    -- K28.5(K)

            end if;

            if ((idle_c(3) and gen_r_r(3)) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"1C" after DLY;                    -- K28.0(R)

            end if;

            if (gen_sp_r = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"4A" after DLY;                    -- D10.2(SP data)

            end if;

            if (gen_spa_r = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"2C" after DLY;                    -- D12.1(SPA data)

            end if;

            if (gen_v_r(3) = '1') then

                TX_DATA_Buffer(7 downto 0) <= X"E8" after DLY;                    -- D8.7(Ver data)

            end if;

        end if;

    end process;


    -- Generate control signal for byte3.

    process (USER_CLK)

    begin

        if (USER_CLK 'event and USER_CLK = '1') then

            TX_CHAR_IS_K_Buffer(0) <= not ((tx_pe_data_v_r(1) and not gen_pad_r(1)) or
                                            gen_snf_r(1)      or
                                            gen_suf_r(1)      or
                                            gen_sp_r          or
                                            gen_spa_r         or
                                            gen_v_r(3)) after DLY;

        end if;

    end process;

end RTL;
