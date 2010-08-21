---------------------------------------------------------------------------------------------------
--
-- Title       : mido
-- Design      : mdio
-- Author      : 0
-- Company     : 0
--
---------------------------------------------------------------------------------------------------
--
-- File        : mido.vhd
-- Generated   : Mon Apr  5 16:43:44 2004
-- From        : interface description file
-- By          : Itf2Vhdl ver. 1.20
--
---------------------------------------------------------------------------------------------------
--
-- Description :
--
---------------------------------------------------------------------------------------------------

--{{ Section below this comment is automatically maintained
--   and may be overwritten
--{entity {mido} architecture {mido}}

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity mdio_c is
    port(
        CLK :   in std_logic;       -- Input clock
        DIV_CLK : in std_logic_vector(4 downto 0);

        START_OP : in std_logic_vector(1 downto 0);
        OPERATION : in std_logic_vector(1 downto 0);
        PHY_ADDR : in std_logic_vector(4 downto 0);
        REG_ADDR : in std_logic_vector(4 downto 0);
        DATA_IN : in std_logic_vector(15 downto 0);
        DATA_OUT : out std_logic_vector(15 downto 0);

        DATA_RDY : out std_logic;
        RUN_OP : in std_logic;
        BUSY : out std_logic;


        MDC     : out std_logic; -- MDIO Clock output
        MDIO_I  : in  std_logic; -- MDIO Input data
        MDIO_O  : out std_logic; -- MDIO Output data
        MDIO_OE : out std_logic  -- MDIO Output Enable, active low


        );
end mdio_c;

--}} End of automatically maintained section

architecture mdio_c of mdio_c is

    constant DIR_IN : std_logic := '1';
    constant DIR_OUT : std_logic := '0';

    constant TURN_AROUND_O : std_logic_vector(0 to 1) := "10";

    constant OP_READ : std_logic_vector(1 downto 0) := "10";
    constant OP_WRITE : std_logic_vector(1 downto 0) := "01";
    constant OP_ADDR : std_logic_vector(1 downto 0) := "00";
    constant OP_READ_INC : std_logic_vector(1 downto 0) := "11";

    type STATE_MDIO_T is (GEN_PREAMBLE, GEN_START, OPCODE, PHY_ADDRESS,
    REG_ADDRESS, TURN_AROUND, DATA, MDIO_DONE);

    signal STATE_MDIO : STATE_MDIO_T;

    signal DIV_CNT : integer range 0 to 31 := 0;
    signal ENABLE_OP : std_logic := '1';
    signal MDC_I : std_logic := '1';
    signal sig_MDIO_I : std_logic;
    signal MDIO_DIR : std_logic := '0';

    signal MDC_FE : std_logic;
    signal MDIO_GO : std_logic := '1';

    signal MDIO_CNT : integer range 0 to 31 := 0;

    signal START_OP_I : std_logic_vector(0 to 1);
    signal OPERATION_I : std_logic_vector(0 to 1);
    signal PHY_ADDR_I, REG_ADDR_I : std_logic_vector(0 to 4);
    signal DATA_IN_I, DATA_OUT_I : std_logic_vector(0 to 15);

    signal OP_DONE : std_logic := '0';

begin

    GEN_CLK: PROCESS(CLK)
    BEGIN
        If CLK'event And CLK = '1'
            Then
            If ENABLE_OP = '1'
                Then
                If DIV_CNT = (CONV_INTEGER(DIV_CLK))
                    Then
                    DIV_CNT <= 0;
                    MDC_I <= Not MDC_I;
                Else
                    DIV_CNT <= DIV_CNT + 1;
                End If;
            Else
                MDC_I <= '1';
                DIV_CNT <= 0;
            End If;
        End If;
    END PROCESS;

    MDC_FE <= '1' When DIV_CNT = (CONV_INTEGER(DIV_CLK)) And MDC_I = '1' Else '0';


    PROCESS(CLK)
    BEGIN
        If CLK'event And CLK = '1'
            Then
            If RUN_OP = '1'
                Then

                START_OP_I <= START_OP;
                PHY_ADDR_I <= PHY_ADDR;
                REG_ADDR_I <= REG_ADDR;
                OPERATION_I <= OPERATION;
                DATA_IN_I <= DATA_IN;
                ENABLE_OP <= '1';
            Else
                If OP_DONE = '1' And MDC_I = '1'
                    Then
                    ENABLE_OP <= '0';
                End If;
            End If;
        End If;
    END PROCESS;

    PROCESS(CLK, MDC_FE, STATE_MDIO)
    BEGIN
        If CLK'event And CLK = '1'
            Then
            If ENABLE_OP = '1'
                Then
                If MDC_FE = '1'
                    Then
                    Case STATE_MDIO is
                        --When WAIT_FOR_START =>
                        --MDIO_DIR <= DIR_OUT;
                        --sig_MDIO_I <= '1';
                        --If MDIO_GO = '1'
                        --	Then
                        --		MDIO_CNT <= 0;
                        --		STATE_MDIO <= GEN_PREAMBLE;
                        --	Else
                        --		STATE_MDIO <= WAIT_FOR_START;
                        --	End If;

                        When GEN_PREAMBLE =>
                           sig_MDIO_I   <= '1';
                           MDIO_DIR <= DIR_OUT;
                        If MDIO_CNT < 31
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= GEN_PREAMBLE;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= GEN_START;
                        End If;

                        When GEN_START =>
                        sig_MDIO_I <= START_OP_I(MDIO_CNT);
                        If MDIO_CNT < 1
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= GEN_START;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= OPCODE;
                        End If;

                        When OPCODE =>
                        sig_MDIO_I <= OPERATION_I(MDIO_CNT);
                        If MDIO_CNT < 1
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= OPCODE;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= PHY_ADDRESS;
                        End If;

                        When PHY_ADDRESS =>
                        sig_MDIO_I <= PHY_ADDR_I(MDIO_CNT);
                        If MDIO_CNT < 4
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= PHY_ADDRESS;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= REG_ADDRESS;
                        End If;

                        When REG_ADDRESS =>
                        sig_MDIO_I <= REG_ADDR_I(MDIO_CNT);
                        If MDIO_CNT < 4
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= REG_ADDRESS;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= TURN_AROUND;
                        End If;

                        When TURN_AROUND =>
                        sig_MDIO_I <= TURN_AROUND_O(MDIO_CNT);
                        If MDIO_CNT < 1
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= TURN_AROUND;
                        Else
                            MDIO_CNT <= 0;
                            STATE_MDIO <= DATA;
                        End If;

                        Case OPERATION_I is
                            When OP_READ | OP_READ_INC =>
                            MDIO_DIR <= DIR_IN;
                            When Others =>
                            MDIO_DIR <= DIR_OUT;
                        End Case;

                        When DATA =>
                        If MDIO_DIR = DIR_IN
                            Then
                            DATA_OUT_I(MDIO_CNT) <= MDIO_I;
                        Else
                            sig_MDIO_I <= DATA_IN_I(MDIO_CNT);
                        End If;
                        If MDIO_CNT < 15
                            Then
                            MDIO_CNT <= MDIO_CNT + 1;
                            STATE_MDIO <= DATA;
                        Else
                            MDIO_CNT <= 0;
                            OP_DONE  <= '1';
                            STATE_MDIO <= MDIO_DONE;
                        End If;
                        
                        When MDIO_DONE =>
                           OP_DONE    <= '1';
                           MDIO_DIR   <= DIR_IN;
                           STATE_MDIO <= GEN_PREAMBLE;

                        When Others =>
                        STATE_MDIO <= GEN_PREAMBLE;
                    End Case;
                End If;
            Else
                MDIO_CNT <= 0;
                OP_DONE <= '0';
                MDIO_DIR <= DIR_IN;
                STATE_MDIO <= GEN_PREAMBLE;
            End If;
        End If;

    END PROCESS;

    BUSY <= ENABLE_OP;

    MDC <= MDC_I;
    MDIO_O <= sig_MDIO_I;
    MDIO_OE <= MDIO_DIR;

    DATA_OUT <= DATA_OUT_I;

end mdio_c;
