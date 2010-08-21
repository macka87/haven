
library IEEE;
use IEEE.std_logic_1164.all;


entity FF_PAIR is
    port(
        CLK                    : in std_logic;    -- flip-flop's clock.
        RST                    : in std_logic;    -- Global Asynchronous Reset.
        CLKEN                  : in std_logic;    -- Clock Enable.
        I                      : in std_logic;    -- Input Data Bit.
        O_REG                  : out std_logic    -- Output Data Bit.
        );
end FF_PAIR;

architecture RTL of FF_PAIR is

    signal I_REG              : std_logic;       -- Input data reclocked onto falling edge of CLK.

begin

    -- purpose: Reclock input from the falling edge.
    RECLOCK_FALLING : process (CLK, RST)
    begin
        if RST = '1' then
            I_REG <= '0';
        elsif CLK'event and CLK = '0' then
            if CLKEN = '1' then
                I_REG <= I;
            end if;
        end if;
    end process RECLOCK_FALLING;


    -- purpose: Reclock again onto the rising edge.
    -- type   : sequential
    RECLOCK_RISING : process (CLK, RST)
    begin
        if RST = '1' then
            O_REG <= '0';
        elsif CLK'event and CLK = '1' then
            if CLKEN = '1' then
                O_REG <= I_REG;
            end if;
        end if;
    end process RECLOCK_RISING;


end RTL;
