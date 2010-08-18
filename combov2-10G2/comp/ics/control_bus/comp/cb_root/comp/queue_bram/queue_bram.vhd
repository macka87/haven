-- queue_bram.vhd : Memory for Control Bus Root queue
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- library containing log2 function
use work.math_pack.all;
use work.bmem_func.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity queue_bram is
   generic(
      ITEMS_B  : integer := 2048 -- Number of items at interface B
   );
   port(
      RESET    : in  std_logic;
      
      -- PPC interface - 64 bit
      CLKA     : in  std_logic;
      REA      : in  std_logic;
      WEA      : in  std_logic;
      ADDRA    : in  std_logic_vector(LOG2(ITEMS_B/4)-1 downto 0);
      DIA      : in  std_logic_vector(63 downto 0);
      DMA      : in  std_logic_vector(7 downto 0);
      DOA_DV   : out std_logic;
      DOA      : out std_logic_vector(63 downto 0);

      -- Control Bus interface - 16 bit, aligned to 32 bits internally
      CLKB     : in  std_logic;
      REB      : in  std_logic;
      WEB      : in  std_logic;
      ADDRB    : in  std_logic_vector(LOG2(ITEMS_B)-1 downto 0);
      DIB      : in  std_logic_vector(15 downto 0);
      DOB_DV   : out std_logic;
      DOB      : out std_logic_vector(15 downto 0)
   );
end entity queue_bram;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture queue_bram_arch of queue_bram is

signal reg_odd    : std_logic;
signal reg_low16  : std_logic_vector(15 downto 0);
signal reg_addrb  : std_logic_vector(LOG2(ITEMS_B)-1 downto 0);
signal sig_addrb  : std_logic_vector(LOG2(ITEMS_B/4)-1 downto 0);
signal reg_addrb10: std_logic_vector(1 downto 0);

signal wea_l      : std_logic;
signal wea_h      : std_logic;
signal web_l      : std_logic;
signal web_h      : std_logic;
signal reb_l      : std_logic;
signal reb_h      : std_logic;
signal dib_l      : std_logic_vector(31 downto 0);
signal dib_h      : std_logic_vector(31 downto 0);
signal dob_l      : std_logic_vector(31 downto 0);
signal dob_h      : std_logic_vector(31 downto 0);
signal dob_dv_l   : std_logic;
signal dob_dv_h   : std_logic;
signal doa_dv_l   : std_logic;
signal doa_dv_h   : std_logic;

signal mux_din    : std_logic_vector(63 downto 0);

begin
   -- Higher part of data (as visible from PPC)
   QUEUE_H: entity work.DP_BMEM_ATTR
   generic map(
      DATA_WIDTH  => 32,
      ITEMS       => ITEMS_B / 4,
      BRAM_TYPE   => 36,
      OUTPUT_REG  => false,
      DEBUG       => false
   )
   port map(
      -- Common interface
      RESET       => RESET,

      -- Interface A
      CLKA        => CLKA,
      PIPE_ENA    => '1',
      REA         => REA,
      WEA         => wea_h,
      ADDRA       => ADDRA,
      DIA         => DIA(63 downto 32),
      DOA_DV      => doa_dv_h,
      DOA         => DOA(63 downto 32),

      -- Interface B
      CLKB        => CLKB,
      PIPE_ENB    => '1',
      REB         => reb_h,
      WEB         => web_h,
      ADDRB       => sig_addrb,
      DIB         => dib_h,
      DOB_DV      => dob_dv_h,
      DOB         => dob_h
   );
   reb_h <= REB and ADDRB(1);
   web_h <= reg_addrb(1) and reg_odd and WEB;
   wea_h <= WEA and DMA(7) and DMA(6) and DMA(5) and DMA(4);
   dib_h <= DIB & reg_low16;   
   
   -- Lower part of data (as visible from PPC)
   QUEUE_L: entity work.DP_BMEM_ATTR
   generic map(
      DATA_WIDTH  => 32,
      ITEMS       => ITEMS_B / 4,
      BRAM_TYPE   => 36,
      OUTPUT_REG  => false,
      DEBUG       => false
   )
   port map(
      -- Common interface
      RESET       => RESET,

      -- Interface A
      CLKA        => CLKA,
      PIPE_ENA    => '1',
      REA         => REA,
      WEA         => wea_l,
      ADDRA       => ADDRA,
      DIA         => DIA(31 downto 0),
      DOA_DV      => doa_dv_l,
      DOA         => DOA(31 downto 0),

      -- Interface B
      CLKB        => CLKB,
      PIPE_ENB    => '1',
      REB         => reb_l,
      WEB         => web_l,
      ADDRB       => sig_addrb,
      DIB         => dib_l,
      DOB_DV      => dob_dv_l,
      DOB         => dob_l
   );
   reb_l <= REB and not ADDRB(1);
   web_l <= (not reg_addrb(1)) and reg_odd and WEB;
   wea_l <= WEA and DMA(3) and DMA(2) and DMA(1) and DMA(0);
   dib_l <= DIB & reg_low16;

   sig_addrb <= reg_addrb(LOG2(ITEMS_B)-1 downto 2) when REB = '0' else
                ADDRB(LOG2(ITEMS_B)-1 downto 2);
   
   dob_mux : entity work.gen_mux
   generic map(
      DATA_WIDTH => 16,
      MUX_WIDTH  => 4
   )
   port map(
      DATA_OUT   => DOB,
      DATA_IN    => mux_din,
      SEL        => reg_addrb10
   );
   mux_din <= dob_h & dob_l;
   
   -- is 1 when odd (high) half of 32bit word should be written
   reg_odd_p : process(CLKB, RESET)
   begin
      if RESET = '1' then 
         reg_odd <= '0';
      elsif CLKB'event and CLKB = '1' then
         if WEB = '1' then
            reg_odd <= not reg_odd;
         end if;
      end if;
   end process;
   
   -- Stores lower part of the word
   reg_low16_p : process(CLKB, RESET)
   begin
      if RESET = '1' then
         reg_low16 <= (others => '0');
      elsif CLKB'event and CLKB = '1' then
         if reg_odd = '0' and WEB = '1' then
            reg_low16 <= DIB;
         end if;
      end if;
   end process;
   
   -- Stores ADDRB for writing purposes
   reg_addrb_p : process(CLKB, RESET)
   begin
      if RESET = '1' then
         reg_addrb <= (others => '0');
      elsif CLKB'event and CLKB = '1' then
         if reg_odd = '0' and WEB = '1' then
            reg_addrb <= ADDRB;
         end if;
      end if;
   end process;
   
   -- Stores two LSBs of ADDRB for reading purposes
   reg_addrb10_p : process(CLKB, RESET)
   begin
      if RESET = '1' then
         reg_addrb10 <= "00";
      elsif CLKB'event and CLKB = '1' then
         reg_addrb10 <= ADDRB(1 downto 0);
      end if;
   end process;

   DOB_DV <= dob_dv_l;
   DOA_DV <= doa_dv_l;

end architecture queue_bram_arch;
