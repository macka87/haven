-- sdram_sim.vhd: DDR SDRAM simulation model
-- Copyright (C) 2006 CESNET
-- Author(s): Pus Viktor <pus@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- README: SPD nets are not connected - no simulation model available
--         16 bit chips are not supported
--         More ChipSelect signals are not supported (only one)
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

entity SDRAM_SIM is
   generic (
      ADDR_BITS : integer := 13;
      COLS_BITS : integer := 12;    -- This is an example for 1G module
      DATA_BITS : integer :=  4     -- 4 or 8
   );

   port (
     DD    : INOUT STD_LOGIC_VECTOR(63 DOWNTO 0) := (OTHERS => 'Z');
     DCB   : INOUT STD_LOGIC_VECTOR( 7 DOWNTO 0) := (OTHERS => 'Z');
     DBA   : IN    STD_LOGIC_VECTOR( 2 DOWNTO 0);
     DQS   : INOUT STD_LOGIC_VECTOR(17 DOWNTO 0) := (OTHERS => 'Z');
     DA    : IN    STD_LOGIC_VECTOR(13 DOWNTO 0);
     DCS_N : IN    STD_LOGIC_VECTOR( 3 DOWNTO 0);
     DCLKE : IN    STD_LOGIC_VECTOR( 1 DOWNTO 0);
     DCAS_N: IN    STD_LOGIC;
     DRAS_N: IN    STD_LOGIC;
     DWE_N : IN    STD_LOGIC;
     DCLK  : IN    STD_LOGIC;
     DCLK_N: IN    STD_LOGIC;
     RESDDR_N:IN   STD_LOGIC;
     DSDA  : INOUT STD_LOGIC;
     DSCLK : IN    STD_LOGIC
  );
end SDRAM_SIM;

-- ----------------------------------------------------------------------
--                    Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of SDRAM_SIM is

   -- register signals - simulating registered memory
   signal reg_DBA        : std_logic_vector(1 downto 0);
   signal reg_DA         : std_logic_vector(ADDR_BITS-1 downto 0);
   signal reg_DCS_N      : std_logic;
   signal reg_DCLKE      : std_logic;
   signal reg_DCAS_N     : std_logic;
   signal reg_DRAS_N     : std_logic;
   signal reg_DWE_N      : std_logic;
   signal reg_DM         : std_logic;

component MT46V32M4 IS
    GENERIC (                                   -- Timing for -75Z CL2
        tCK       : TIME    :=  7.500 ns;
        tCH       : TIME    :=  3.375 ns;       -- 0.45*tCK
        tCL       : TIME    :=  3.375 ns;       -- 0.45*tCK
        tDH       : TIME    :=  0.500 ns;
        tDS       : TIME    :=  0.500 ns;
        tIH       : TIME    :=  0.900 ns;
        tIS       : TIME    :=  0.900 ns;
        tMRD      : TIME    := 15.000 ns;
        tRAS      : TIME    := 40.000 ns;
        --tRAP      : TIME    := 20.000 ns;
        tRC       : TIME    := 65.000 ns;
        tRFC      : TIME    := 75.000 ns;
        tRCD      : TIME    := 20.000 ns;
        tRP       : TIME    := 20.000 ns;
        tRRD      : TIME    := 15.000 ns;
        tWR       : TIME    := 15.000 ns;
        addr_bits : INTEGER := 12;
        data_bits : INTEGER :=  4;
        cols_bits : INTEGER := 11
    );
    PORT (
        Dq    : INOUT STD_LOGIC_VECTOR (data_bits - 1 DOWNTO 0) := (OTHERS => 'Z');
        Dqs   : INOUT STD_LOGIC := 'Z';
        Addr  : IN    STD_LOGIC_VECTOR (addr_bits - 1 DOWNTO 0);
        Ba    : IN    STD_LOGIC_VECTOR             (1 DOWNTO 0);
        Clk   : IN    STD_LOGIC;
        Clk_n : IN    STD_LOGIC;
        Cke   : IN    STD_LOGIC;
        Cs_n  : IN    STD_LOGIC;
        Ras_n : IN    STD_LOGIC;
        Cas_n : IN    STD_LOGIC;
        We_n  : IN    STD_LOGIC;
        Dm    : IN    STD_LOGIC
    );
END component;


begin
   ddr_chip_gen: for i in 0 to (64/DATA_BITS)-1 generate
      sdram: MT46V32M4
      generic map(
        tCK             => 10  ns,
        tCH             => 4.5 ns,
        tCL             => 4.5 ns,
        tDH             => 0.6 ns,
        tDS             => 0.6 ns,
        tIH             => 1.1 ns,
        tIS             => 1.1 ns,
        tMRD            => 20  ns,
        tRAS            => 50  ns,
        --tRAP      : TIME    := 20.000 ns;
        tRC             => 70  ns,
        tRFC            => 80  ns,
        tRCD            => 20  ns,
        tRP             => 20  ns,
        tRRD            => 15  ns,
        tWR             => 15  ns,
        addr_bits       => ADDR_BITS,
        data_bits       => DATA_BITS,
        cols_bits       => COLS_BITS
      )
      port map (
         Dq             => DD(DATA_BITS*(i+1) - 1 downto DATA_BITS*i),
         DQS            => DQS(i + (i/8)),

         BA             => reg_DBA,
         addr           => reg_DA,
         CS_N           => reg_DCS_N,
         CKE            => reg_DCLKE,
         CAS_N          => reg_DCAS_N,
         RAS_N          => reg_DRAS_N,
         WE_N           => reg_DWE_N,
         CLK            => DCLK,
         CLK_N          => DCLK_N,
         dm             => '0'
      );
   end generate;

   dQS_chip_gen: for i in 0 to (8/DATA_BITS)-1 generate
      sdram: MT46V32M4
      generic map(
        tCK             => 10  ns,
        tCH             => 4.5 ns,
        tCL             => 4.5 ns,
        tDH             => 0.6 ns,
        tDS             => 0.6 ns,
        tIH             => 1.1 ns,
        tIS             => 1.1 ns,
        tMRD            => 20  ns,
        tRAS            => 50  ns,
        --tRAP      : TIME    := 20.000 ns;
        tRC             => 70  ns,
        tRFC            => 80  ns,
        tRCD            => 20  ns,
        tRP             => 20  ns,
        tRRD            => 15  ns,
        tWR             => 15  ns,
        addr_bits       => ADDR_BITS,
        data_bits       => DATA_BITS,
        cols_bits       => COLS_BITS
      )
      port map (
         Dq             => DCB(DATA_BITS*(i+1) - 1 downto DATA_BITS*i),
         DQS            => DQS((i+1)*9 - 1),

         BA             => reg_DBA,
         addr           => reg_DA,
         CS_N           => reg_DCS_N,
         CKE            => reg_DCLKE,
         CAS_N          => reg_DCAS_N,
         RAS_N          => reg_DRAS_N,
         WE_N           => reg_DWE_N,
         CLK            => DCLK,
         CLK_N          => DCLK_N,
         dm             => '0'
      );
   end generate;

   reg_DBA     <= DBA(1 downto 0) after 10 ns;
   reg_DA      <= DA(ADDR_BITS-1 downto 0) after 10 ns;
   reg_DCS_N   <= DCS_N(0) after 10 ns;
   reg_DCLKE   <= DCLKE(0) after 10 ns;
   reg_DCAS_N  <= DCAS_N after 10 ns;
   reg_DRAS_N  <= DRAS_N after 10 ns;
   reg_DWE_N   <= DWE_N after 10 ns;

end architecture behavioral;
