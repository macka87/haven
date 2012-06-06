-----------------------------------------------------------------------------------
--                                                                               --
--      Title        : Pseudo Random Number Generator (TinyMT32)                 --
--      Module Name  : TINYMT32_GEN                                              --
--      Version      : 0.0.1                                                     --
--      Created      : 2012/3/24                                                 --
--      File Name    : tinymt32_gen.vhd                                          --
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
use     work.TINYMT32.RANDOM_NUMBER_TYPE;
use     work.TINYMT32.PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
entity  TINYMT32_GEN is
    port (
        CLK         : in  std_logic;
        RST         : in  std_logic;
        INIT        : in  std_logic;
        INIT_PARAM  : in  PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
        RND_RUN     : in  std_logic;
        RND_VAL     : out std_logic;
        RND_NUM     : out RANDOM_NUMBER_TYPE
    );
end     TINYMT32_GEN;
-----------------------------------------------------------------------------------
--
-----------------------------------------------------------------------------------
library ieee;
use     ieee.std_logic_1164.all;
use     ieee.numeric_std.all;
use     work.TINYMT32.all;
architecture RTL of TINYMT32_GEN is
    constant  DEFAULT_PARAM    : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE :=
                                 NEW_PSEUDO_RANDOM_NUMBER_GENERATOR(
                                     X"8f7011ee",
                                     X"fc78ff1f",
                                     X"3793fdff",
                                     TO_SEED_TYPE(1)
                                 );
    signal    curr_status      : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    signal    status_valid     : std_logic;
begin
    process(CLK, RST)
        variable next_status   : PSEUDO_RANDOM_NUMBER_GENERATOR_TYPE;
    begin
        if (RST = '1') then
                curr_status  <= DEFAULT_PARAM;
                status_valid <= '0';
                RND_VAL      <= '0';
                RND_NUM      <= (others => '0');
        elsif (CLK'event and CLK = '1') then
            if (INIT = '1') then
                curr_status  <= INIT_PARAM;
                status_valid <= '0';
                RND_VAL      <= '0';
                RND_NUM      <= (others => '0');
            else
                if (RND_RUN = '1') then
                    next_status := curr_status;
                    NEXT_PSEUDO_RANDOM_NUMBER_GENERATOR(next_status);
                    curr_status  <= next_status;
                    status_valid <= '1';
                else
                    status_valid <= '0';
                end if;
                if (status_valid = '1') then
                    RND_NUM <= GENERATE_TEMPER(curr_status);
                    RND_VAL <= '1';
                else
                    RND_VAL <= '0';
                end if;
            end if;
        end if;
    end process;
end RTL;
