-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.all;
use     std.textio.all;
use     work.TINYMT32.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture arch of TESTBENCH is
    constant  OUTPUT_WIDTH : integer := 0;
    constant  PERIOD       : time := 10 ns;
    constant  DELAY        : time := 1 ns;
    
    
    signal    CLK        : std_logic;
    signal    RST        : std_logic;
    signal    INIT       : std_logic;
    signal    SEED       : std_logic_vector(31 downto 0);
    signal    RND_RUN    : std_logic;
    signal    RND_VAL    : std_logic;
    signal    RND_NUM    : std_logic_vector(OUTPUT_WIDTH-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                  Mersenne Twister N Generator
   -- -------------------------------------------------------------------------
   uut: entity work.MT_N
      generic map (
         OUTPUT_WIDTH      => OUTPUT_WIDTH
      )
      port map(
         CLK         => CLK,
         RST         => RST,
         INIT        => INIT,
         SEED        => SEED,
         RND_RUN     => RND_RUN,
         RND_VAL     => RND_VAL,
         RND_NUM     => RND_NUM
       );
    
    process begin
        CLK <= '1'; wait for PERIOD/2;
        CLK <= '0'; wait for PERIOD/2;
    end process;

    process
        
        procedure WAIT_CLK(CNT:integer) is
        begin
            for i in 1 to CNT loop 
                wait until (CLK'event and CLK = '1'); 
            end loop;
            wait for DELAY;
        end WAIT_CLK;
         
    begin
        RST       <= '1';
        INIT      <= '0';        
        RND_RUN   <= '0';
        WAIT_CLK(10);
        RST       <= '0';
        WAIT_CLK(10);

        INIT      <= '1';
        SEED      <= X"00000001";
        
        WAIT_CLK(1);
        INIT      <= '0';
        WAIT_CLK(1);

        RND_RUN   <= '1';
        wait;
    end process;
end arch;
