-----------------------------------------------------------------------------------
--                                                                               --
--      Title        : Test Bench for MT32_GEN                                   --
--      Module Name  : TEST_BENCH                                                --
--      Version      : 0.0.3                                                     --
--      Created      : 2012/3/28                                                 --
--      File Name    : TEST_BENCH.vhd                                            --
--      Author       : Ichiro Kawazome <ichiro_k@ca2.so-net.ne.jp>               --
--                                                                               --
--      Copyright (C) 2012 Ichiro Kawazome                                       --
--      All rights reserved.                                                     --
--                                                                               --
--      Redistribution and use in source and binary forms, with or without       --
--      modification, are permitted provided that the following conditions       --
--      are met:                                                                 --
--                                                                               --
--        1. Redistributions of source code must retain the above copyright      --
--           notice, this list of conditions and the following disclaimer.       --
--                                                                               --
--        2. Redistributions in binary form must reproduce the above copyright   --
--           notice, this list of conditions and the following disclaimer in     --
--           the documentation and/or other materials provided with the          --
--           distribution.                                                       --
--                                                                               --
--      THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      --
--      "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        --
--      LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    --
--      A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT    --
--      OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,    --
--      SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         --
--      LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    --
--      DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    --
--      THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      --
--      (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    --
--      OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     --
--                                                                               --
-----------------------------------------------------------------------------------
library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.all;
use     std.textio.all;
use     work.TINYMT32.all;
entity  TESTBENCH is
end     TESTBENCH;
architecture MODEL of TESTBENCH is
    component  TINYMT32_GEN
        port (
            CLK         : in  std_logic;
            RST         : in  std_logic;
            INIT        : in  std_logic;
            INIT_PARAM  : in  PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
            RND_RUN     : in  std_logic;
            RND_VAL     : out std_logic;
            RND_NUM     : out RANDOM_NUMBER_TYPE
        );
    end component;
    constant  PERIOD    : time := 10 ns;
    constant  DELAY     : time := 1 ns;
    signal    CLK       : std_logic;
    signal    RST       : std_logic;
    signal    INIT      : std_logic;
    signal    INIT_PARAM: PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    signal    RND_RUN   : std_logic;
    signal    RND_VAL   : std_logic;
    signal    RND_NUM   : RANDOM_NUMBER_TYPE;
begin
    U: TINYMT32_GEN
        port map(
            CLK         => CLK,
            RST         => RST,
            INIT        => INIT,
            INIT_PARAM  => INIT_PARAM,
            RND_RUN     => RND_RUN,
            RND_VAL     => RND_VAL,
            RND_NUM     => RND_NUM
        );
    
    process begin
        CLK <= '1'; wait for PERIOD/2;
        CLK <= '0'; wait for PERIOD/2;
    end process;

    process
        ---------------------------------------------------------------------------
        -- unsigned to hex string.
        ---------------------------------------------------------------------------
        function TO_HEX_STRING(arg:unsigned;len:integer;space:character) return STRING is
            variable str   : STRING(len downto 1);
            variable value : unsigned(arg'length-1 downto 0);
        begin
            value  := arg;
            for i in str'right to str'left loop
                if (value > 0) then
                    case (to_integer(value mod 16)) is
                        when  0     => str(i) := '0';
                        when  1     => str(i) := '1';
                        when  2     => str(i) := '2';
                        when  3     => str(i) := '3';
                        when  4     => str(i) := '4';
                        when  5     => str(i) := '5';
                        when  6     => str(i) := '6';
                        when  7     => str(i) := '7';
                        when  8     => str(i) := '8';
                        when  9     => str(i) := '9';
                        when 10     => str(i) := 'a';
                        when 11     => str(i) := 'b';
                        when 12     => str(i) := 'c';
                        when 13     => str(i) := 'd';
                        when 14     => str(i) := 'e';
                        when 15     => str(i) := 'f';
                        when others => str(i) := 'X';
                    end case;
                else
                    if (i = str'right) then
                        str(i) := '0';
                    else
                        str(i) := space;
                    end if;
                end if;
                value := value / 16;
            end loop;
            return str;
        end function;
        ---------------------------------------------------------------------------
        -- unsigned to decimal string.
        ---------------------------------------------------------------------------
        function TO_DEC_STRING(arg:unsigned;len:integer;space:character) return STRING is
            variable str   : STRING(len downto 1);
            variable value : unsigned(arg'length-1 downto 0);
        begin
            value  := arg;
            for i in str'right to str'left loop
                if (value > 0) then
                    case (to_integer(value mod 10)) is
                        when 0      => str(i) := '0';
                        when 1      => str(i) := '1';
                        when 2      => str(i) := '2';
                        when 3      => str(i) := '3';
                        when 4      => str(i) := '4';
                        when 5      => str(i) := '5';
                        when 6      => str(i) := '6';
                        when 7      => str(i) := '7';
                        when 8      => str(i) := '8';
                        when 9      => str(i) := '9';
                        when others => str(i) := 'X';
                    end case;
                else
                    if (i = str'right) then
                        str(i) := '0';
                    else
                        str(i) := space;
                    end if;
                end if;
                value := value / 10;
            end loop;
            return str;
        end function;
        ---------------------------------------------------------------------------
        -- unsigned to decimal string
        ---------------------------------------------------------------------------
        function TO_DEC_STRING(arg:unsigned;len:integer) return STRING is
        begin
            return  TO_DEC_STRING(arg,len,' ');
        end function;
        ---------------------------------------------------------------------------
        -- unsigned to decimal string
        ---------------------------------------------------------------------------
        function TO_HEX_STRING(arg:unsigned;len:integer) return STRING is
        begin
            return  TO_HEX_STRING(arg,len,'0');
        end function;
        ---------------------------------------------------------------------------
        -- real number to decimal string.
        ---------------------------------------------------------------------------
        function TO_DEC_STRING(arg:real;len1,len2:integer) return STRING is
            variable str   : STRING(len2-1 downto 0);
            variable i,n,p : integer;
        begin
            i := integer(arg);
            if    real(i) = arg then
                n := i;
            elsif i > 0 and real(i) > arg then
                n := i-1;  
            elsif i < 0 and real(i) < arg then
                n := i+1;
            else  
                n := i;
            end if;
            p := integer((arg-real(n))*(10.0**len2));
            return  TO_DEC_STRING(to_unsigned(n,len1-len2-1),len1-len2-1,' ') & "." & 
                    TO_DEC_STRING(to_unsigned(p,32),len2,'0');
        end function;
        ---------------------------------------------------------------------------
        -- convert Random Number to real.
        ---------------------------------------------------------------------------
        function TO_REAL(arg:RANDOM_NUMBER_TYPE) return real is
          variable result: real := 0.0;
        begin
            for i in arg'range loop
                result := result + result;
                if (arg(i) = '1') then
                    result := result + 1.0;
                end if;
            end loop;
            return result;
        end function;
        ---------------------------------------------------------------------------
        -- Pseudo Random Number Generator Initalize Parameters.
        ---------------------------------------------------------------------------
        constant seed      : SEED_TYPE           := X"00000001";
        constant mat1      : SEED_TYPE           := X"8f7011ee";
        constant mat2      : SEED_TYPE           := X"fc78ff1f";
        constant tmat      : RANDOM_NUMBER_TYPE  := X"3793fdff";
        constant init_key  : SEED_VECTOR(0 to 0) := (0 => seed);
        variable param     : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE :=
                             NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(mat1,mat2,tmat,seed);
        ---------------------------------------------------------------------------
        -- Random number
        ---------------------------------------------------------------------------
        variable num       : real;
        ---------------------------------------------------------------------------
        -- for display
        ---------------------------------------------------------------------------
        constant TAG       : STRING(1 to 1) := " ";
        constant SPACE     : STRING(1 to 1) := " ";
        variable text_line : LINE;
        ---------------------------------------------------------------------------
        -- 
        ---------------------------------------------------------------------------
        procedure WAIT_CLK(CNT:integer) is
        begin
            for i in 1 to CNT loop 
                wait until (CLK'event and CLK = '1'); 
            end loop;
            wait for DELAY;
        end WAIT_CLK;
        ---------------------------------------------------------------------------
        -- 
        ---------------------------------------------------------------------------
        variable count_run : integer;
        variable count_val : integer;
        variable count_max : integer;
        constant RUN_WAIT  : integer := 1;
    begin
        RST       <= '1';
        INIT      <= '0';        
        RND_RUN   <= '0';
        WAIT_CLK(10);
        RST       <= '0';
        WAIT_CLK(10);

     -- WRITE(text_line, TO_HEX_STRING(unsigned(TO_01(param.status(0))),10) & SPACE);
     -- WRITE(text_line, TO_HEX_STRING(unsigned(TO_01(param.status(1))),10) & SPACE);
     -- WRITE(text_line, TO_HEX_STRING(unsigned(TO_01(param.status(2))),10) & SPACE);
     -- WRITE(text_line, TO_HEX_STRING(unsigned(TO_01(param.status(3))),10));
     -- WRITELINE(OUTPUT, text_line);

        INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(param,mat1,mat2,tmat,seed);
        --WRITE(text_line, "tinymt32 0x" & TO_HEX_STRING(unsigned(param.mat1),8) & SPACE);
        --WRITE(text_line,          "0x" & TO_HEX_STRING(unsigned(param.mat2),8) & SPACE);
        --WRITE(text_line,          "0x" & TO_HEX_STRING(unsigned(param.tmat),8) & SPACE);
        --WRITE(text_line,     "seed = " & TO_DEC_STRING(unsigned(seed      ),1));
        --WRITELINE(OUTPUT, text_line);
        --WRITE(text_line, "32-bit unsigned integers r, where 0 <= r < 2^32" & SPACE);
        --WRITELINE(OUTPUT, text_line);
        INIT      <= '1';
        INIT_PARAM<= param;
        WAIT_CLK(1);
        INIT      <= '0';
        WAIT_CLK(1);

        RND_RUN   <= '1';
        wait;
    end process;
end MODEL;
