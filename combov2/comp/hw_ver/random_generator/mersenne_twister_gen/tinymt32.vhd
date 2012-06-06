-----------------------------------------------------------------------------------
--                                                                               --
--      Title        : Pseudo Random Number Generator Package(TinyMT32)          --
--      Package Name : TINYMT32                                                  --
--      Version      : 0.0.1                                                     --
--      Created      : 2012/3/24                                                 --
--      File Name    : tinymt32.vhd                                              --
--      Author       : Ichiro Kawazome <ichiro_k@ca2.so-net.ne.jp>               --
--      Description  : VHDL package for TinyMT32.                                --
--                     Tiny Mersenne Twister only 127 bit internal state.        --
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
package TINYMT32 is
    -------------------------------------------------------------------------------
    -- Type of Random Number.
    -------------------------------------------------------------------------------
    subtype  RANDOM_NUMBER_TYPE   is unsigned(31 downto 0);
    type     RANDOM_NUMBER_VECTOR is array(integer range <>) of RANDOM_NUMBER_TYPE;
    function TO_RANDOM_NUMBER_TYPE(arg:integer) return RANDOM_NUMBER_TYPE;
    -------------------------------------------------------------------------------
    -- Type of Seed Number for Pseudo Random Number Generator.
    -------------------------------------------------------------------------------
    subtype  SEED_TYPE            is unsigned(31 downto 0);
    type     SEED_VECTOR          is array(integer range <>) of SEED_TYPE;
    function TO_SEED_TYPE(arg:integer) return SEED_TYPE;
    -------------------------------------------------------------------------------
    -- tinymt32 internal state vector and parameters.
    -------------------------------------------------------------------------------
    type     PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE is record
        status  : RANDOM_NUMBER_VECTOR(0 to 3);
        mat1    : SEED_TYPE;
        mat2    : SEED_TYPE;
        tmat    : RANDOM_NUMBER_TYPE;
    end record;    
    -------------------------------------------------------------------------------
    -- Generates instance for Pseudo Random Number Generator.
    -------------------------------------------------------------------------------
    function  NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
                 mat1      :       SEED_TYPE;
                 mat2      :       SEED_TYPE;
                 tmat      :       RANDOM_NUMBER_TYPE;
                 seed      :       SEED_TYPE
    )            return            PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    function  NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
                 mat1      :       SEED_TYPE;
                 mat2      :       SEED_TYPE;
                 tmat      :       RANDOM_NUMBER_TYPE;
                 seed      :       SEED_VECTOR
    )            return            PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    -------------------------------------------------------------------------------
    -- Initialize Pseudo Random Number Generator.
    -------------------------------------------------------------------------------
    procedure INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
                 mat1      : in    SEED_TYPE;
                 mat2      : in    SEED_TYPE;
                 tmat      : in    RANDOM_NUMBER_TYPE;
                 seed      : in    SEED_TYPE
    );
    procedure INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
                 mat1      : in    SEED_TYPE;
                 mat2      : in    SEED_TYPE;
                 tmat      : in    RANDOM_NUMBER_TYPE;
                 seed      : in    SEED_VECTOR
    );
    -------------------------------------------------------------------------------
    -- This function changes internal state of tinymt32.
    -- Users should not call this function directly.
    -------------------------------------------------------------------------------
    procedure NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    );
    -------------------------------------------------------------------------------
    -- This function outputs 32-bit unsigned integer from internal state.
    -- Users should not call this function directly.
    -------------------------------------------------------------------------------
    function  GENERATE_TEMPER(
                 generator : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    )            return      RANDOM_NUMBER_TYPE;
    -------------------------------------------------------------------------------
    -- Generates a random number
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_NUMBER(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   RANDOM_NUMBER_TYPE
    );
    -------------------------------------------------------------------------------
    -- Generates a random number on (std_logic_vector).
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_STD_LOGIC_VECTOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   std_logic_vector
    );
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,0x7fffffff]-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_INT31(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   integer
    );
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,1]-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL1(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    );
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,1)-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL2(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    );
    -------------------------------------------------------------------------------
    -- Generates a random number on (0,1)-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL3(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    );
end     TINYMT32;
-----------------------------------------------------------------------------------
-- 
-----------------------------------------------------------------------------------
library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.all;
package body TINYMT32 is
    -------------------------------------------------------------------------------
    -- Period parameters
    -------------------------------------------------------------------------------
    constant  MEXP            : integer := 127;
    constant  SH0             : integer :=   1;
    constant  SH1             : integer :=  10;
    constant  SH8             : integer :=   8;
    constant  MASK            : RANDOM_NUMBER_TYPE := (RANDOM_NUMBER_TYPE'high => '0', others => '1');
    constant  LINEARITY_CHECK : boolean := FALSE;
    constant  MIN_LOOP        : integer :=   8;
    constant  PRE_LOOP        : integer :=   8;
    -------------------------------------------------------------------------------
    -- Convert from integer to SEED_TYPE.
    -------------------------------------------------------------------------------
    function  TO_SEED_TYPE(arg:integer) return SEED_TYPE is
    begin
        return to_unsigned(arg,SEED_TYPE'length);
    end function;
    -------------------------------------------------------------------------------
    -- Convert from integer to RANDOM_NUMBER_TYPE.
    -------------------------------------------------------------------------------
    function  TO_RANDOM_NUMBER_TYPE(arg:integer) return RANDOM_NUMBER_TYPE is
    begin
        return to_unsigned(arg,RANDOM_NUMBER_TYPE'length);
    end function;
    -------------------------------------------------------------------------------
    -- Convert from Random Number to real.
    ---------------------------------------------------------------------------
    function  TO_REAL(arg:RANDOM_NUMBER_TYPE) return real is
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
    -------------------------------------------------------------------------------
    -- RANDOM_NUMBER_TYPE multiplied by integer.
    -------------------------------------------------------------------------------
    function MUL_K(k:integer;arg:RANDOM_NUMBER_TYPE) return RANDOM_NUMBER_TYPE is
        variable tmp : unsigned(2*RANDOM_NUMBER_TYPE'length-1 downto 0);
    begin
        tmp := arg * TO_RANDOM_NUMBER_TYPE(k);
        return tmp(RANDOM_NUMBER_TYPE'range);
    end function;
    -------------------------------------------------------------------------------
    -- Generates instance for Pseudo Random Number Generator with a seed.
    -------------------------------------------------------------------------------
    function  NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
        mat1    : SEED_TYPE;
        mat2    : SEED_TYPE;
        tmat    : RANDOM_NUMBER_TYPE;
        seed    : SEED_TYPE
    )   return    PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    is
        variable generator : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    begin
        INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator,mat1,mat2,tmat,seed);
        return generator;
    end function;
    -------------------------------------------------------------------------------
    -- Generates instance for Pseudo Random Number Generator by array.
    -------------------------------------------------------------------------------
    function  NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
        mat1    : SEED_TYPE;
        mat2    : SEED_TYPE;
        tmat    : RANDOM_NUMBER_TYPE;
        seed    : SEED_VECTOR
    )   return    PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    is
        variable generator : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    begin
        INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator,mat1,mat2,tmat,seed);
        return generator;
    end function;
    -------------------------------------------------------------------------------
    -- This function certificate the period of 2^127-1.
    -------------------------------------------------------------------------------
    procedure period_certification(generator:inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE) is
    begin 
        if ((generator.status(0) and MASK) = 0) and
            (generator.status(1)           = 0) and
            (generator.status(2)           = 0) and
            (generator.status(3)           = 0) then
             generator.status(0) := TO_RANDOM_NUMBER_TYPE(84); -- 'T'
	     generator.status(1) := TO_RANDOM_NUMBER_TYPE(57); -- 'I';
	     generator.status(2) := TO_RANDOM_NUMBER_TYPE(78); -- 'N';
	     generator.status(3) := TO_RANDOM_NUMBER_TYPE(89); -- 'Y';
        end if;
    end procedure;
    -------------------------------------------------------------------------------
    -- Initialize Pseudo Random Number Generator with a seed.
    -------------------------------------------------------------------------------
    procedure INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
                 mat1      : in    SEED_TYPE;
                 mat2      : in    SEED_TYPE;
                 tmat      : in    RANDOM_NUMBER_TYPE;
                 seed      : in    SEED_TYPE
    ) is
    begin 
        generator.mat1      := mat1;
        generator.mat2      := mat2;
        generator.tmat      := tmat;
        generator.status(0) := seed;
        generator.status(1) := mat1;
        generator.status(2) := mat2;
        generator.status(3) := tmat;
        for i in 1 to MIN_LOOP-1 loop
            generator.status(i mod 4) := generator.status(i mod 4) xor
                                         (MUL_K(1812433253,
                                               ((generator.status((i-1) mod 4)) xor
                                                (generator.status((i-1) mod 4) srl 30))) + i);
        end loop;
        period_certification(generator);
        for i in 0 to PRE_LOOP-1 loop
           NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        end loop;
    end procedure;
    -------------------------------------------------------------------------------
    -- Initialize Pseudo Random Number Generator by array.
    -------------------------------------------------------------------------------
    procedure INIT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
                 mat1      : in    SEED_TYPE;
                 mat2      : in    SEED_TYPE;
                 tmat      : in    RANDOM_NUMBER_TYPE;
                 seed      : in    SEED_VECTOR
    ) is
        constant lag       : integer := 1;
        constant mid       : integer := 1;
        constant size      : integer := 4;
        variable i,j       : integer;
        variable count     : integer;
        variable r         : RANDOM_NUMBER_TYPE;
        alias    init_key  : SEED_VECTOR(1 to seed'length) is seed;
        function ini_func1(x:RANDOM_NUMBER_TYPE) return RANDOM_NUMBER_TYPE is
        begin 
            return MUL_K(1664525   ,(x xor (x srl 27)));
        end function;
        function ini_func2(x:RANDOM_NUMBER_TYPE) return RANDOM_NUMBER_TYPE is
        begin 
            return MUL_K(1566083941,(x xor (x srl 27)));
        end function;
    begin
        generator.mat1      := mat1;
        generator.mat2      := mat2;
        generator.tmat      := tmat;
        generator.status(0) := TO_RANDOM_NUMBER_TYPE(0);
        generator.status(1) := mat1;
        generator.status(2) := mat2;
        generator.status(3) := tmat;
        if (init_key'length + 1 > MIN_LOOP) then
            count := init_key'length + 1;
        else
            count := MIN_LOOP;
        end if;
        i := 0;
        for j in 0 to count-1 loop
            r := ini_func1(generator.status(i) xor
                           generator.status((i+mid) mod size) xor
                           generator.status((i+size-1) mod size));
            generator.status((i+mid    ) mod size) := generator.status((i+mid    ) mod size) + r;
            if    (j = 0) then
                r := r + init_key'length;
            elsif (init_key'low <= j and j <= init_key'high) then
                r := r + init_key(j) + i;
            else
                r := r + i;
            end if;
            generator.status((i+mid+lag) mod size) := generator.status((i+mid+lag) mod size) + r;
            generator.status(i) := r;
            i := (i + 1) mod size;
        end loop;
        for j in 0 to size-1 loop
            r := ini_func2(generator.status(i) +
                           generator.status((i+mid   ) mod size) +
                           generator.status((i+size-1) mod size));
            generator.status((i+mid    ) mod size) := generator.status((i+mid    ) mod size) xor r;
            r := r - i;
            generator.status((i+mid+lag) mod size) := generator.status((i+mid+lag) mod size) xor r;
            generator.status(i) := r;
            i := (i + 1) mod size;
        end loop;
        period_certification(generator);
        for i in 0 to PRE_LOOP-1 loop
            NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        end loop;
    end procedure;
    -------------------------------------------------------------------------------
    -- Generate next stateus
    -------------------------------------------------------------------------------
    procedure NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(
        variable generator  : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    ) is
        variable x          :       RANDOM_NUMBER_TYPE;
        variable y          :       RANDOM_NUMBER_TYPE;
    begin 
        x := (generator.status(0) and MASK) xor generator.status(1) xor generator.status(2);
        y :=  generator.status(3);
        x := x xor (x sll SH0);
        y := y xor (y srl SH0) xor x;
        generator.status(0) := generator.status(1);
        generator.status(1) := generator.status(2);
        generator.status(2) := x xor (y sll SH1);
        generator.status(3) := y;
        if (y(0) = '1') then
            generator.status(1) := generator.status(1) xor generator.mat1;
            generator.status(2) := generator.status(2) xor generator.mat2;
        end if;
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number
    -------------------------------------------------------------------------------
    function GENERATE_TEMPER(
                 generator  :       PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE
    )            return             RANDOM_NUMBER_TYPE
    is
        variable t0         :       RANDOM_NUMBER_TYPE;
        variable t1         :       RANDOM_NUMBER_TYPE;
    begin
        t0 := generator.status(3);
        if (LINEARITY_CHECK) then
            t1 := generator.status(0) xor (generator.status(2) srl SH8);
        else
            t1 := generator.status(0)  +  (generator.status(2) srl SH8);
        end if;
        t0 := t0 xor t1;
        if (t1(0) = '1') then
            t0 := t0 xor generator.tmat;
        end if;
        return t0;
    end function;
    -------------------------------------------------------------------------------
    -- Generates a random number
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_NUMBER(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   RANDOM_NUMBER_TYPE
    ) is
    begin 
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        number := GENERATE_TEMPER(generator);
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number on (std_logic_vector).
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_STD_LOGIC_VECTOR(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   std_logic_vector
    ) is
        variable word      :       RANDOM_NUMBER_TYPE;
        variable number_t  :       std_logic_vector(number'length-1 downto 0);
    begin
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        word := GENERATE_TEMPER(generator);
        for i in number_t'range loop
            if (word(i) = '1') then
                number_t(i) := '1';
            else
                number_t(i) := '0';
            end if;
        end loop;  
        number := number_t;
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,0x7fffffff]-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_INT31(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   integer
    ) is
        variable word      :       RANDOM_NUMBER_TYPE;
    begin
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        word := GENERATE_TEMPER(generator);
        number := to_integer(word(31 downto 1));
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,1]-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL1(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    ) is
        variable word      :       RANDOM_NUMBER_TYPE;
    begin
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        word := GENERATE_TEMPER(generator);
        number := (1.0/4294967295.0)*TO_REAL(word);
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number on [0,1)-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL2(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    ) is
        variable word      :       RANDOM_NUMBER_TYPE;
    begin
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        word := GENERATE_TEMPER(generator);
        number := (1.0/4294967296.0)*TO_REAL(word);
    end procedure;
    -------------------------------------------------------------------------------
    -- Generates a random number on (0,1)-real-interval.
    -------------------------------------------------------------------------------
    procedure GENERATE_RANDOM_REAL3(
        variable generator : inout PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        variable number    : out   real
    ) is
        variable word      :       RANDOM_NUMBER_TYPE;
    begin
        NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(generator);
        word := GENERATE_TEMPER(generator);
        number := (1.0/4294967296.0)*(0.5+TO_REAL(word));
    end procedure;
end     TINYMT32;
