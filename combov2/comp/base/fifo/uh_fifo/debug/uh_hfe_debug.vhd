--
-- uh_hfe_debug.vhd: Unified Header FIFO, UHs are sent to sw via local bus
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Filip Hofer fil@liberouter.org
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
library unisim;
use unisim.all;

entity UH_FIFO is
   port(
      -- HFE interface
      HFE_DOUT   : in  std_logic_vector(15 downto 0); -- SOR data output
      HFE_ADDR   : in  std_logic_vector(5 downto 0);  -- SOR address
      HFE_RDY    : out std_logic;   -- Control signals
      HFE_REQ    : in  std_logic;
      HFE_WEN    : in  std_logic;
      HFE_CLK    : in  std_logic;

      -- LUP interface
      LUP_SR_VALID    : out std_logic;       -- If cell contains unfied header
      LUP_SR_CLEAN    : in  std_logic;       -- Clean addressed cell
      LUP_DATA        : out std_logic_vector(31 downto 0); -- UH data
      LUP_ADDR        : in  std_logic_vector(8 downto 0);  -- Cell addr.
      LUP_CLK         : in  std_logic;

       -- BLOCK RAM READING INTERFACE
      LB_CLK      : in  std_logic;
      ADDRB       : in  std_logic_vector (9 downto 0);
      DOB         : out std_logic_vector (15 downto 0);
      DIB         : in  std_logic_vector (15 downto 0);
      web         : in  std_logic;
      enb         : in  std_logic;

      RESET      : in std_logic
   );
end UH_FIFO;

architecture debug of UH_FIFO is

signal hfe_block        : std_logic_vector(3 downto 0);
signal hfe_block_aux    : std_logic_vector(3 downto 0);
signal lup_block        : std_logic_vector(3 downto 0);
signal ready            : std_logic_vector(15 downto 0);
signal hfe_allocated    : std_logic;
signal addra_i          : std_logic_vector(9 downto 0);
signal write_i          : std_logic;

signal gnd_bus          : std_logic_vector(31 downto 0);
signal gnd              : std_logic;
signal pwr              : std_logic;
signal uh_valid         : std_logic;
signal uh_clean         : std_logic;
signal hfe_is_producing : std_logic;

component RAMB16_S18_S18
   port (
      ADDRA: IN std_logic_vector(9 downto 0);
      ADDRB: IN std_logic_vector(9 downto 0);
      DIA:   IN std_logic_vector(15 downto 0);
      DIB:   IN std_logic_vector(15 downto 0);
      DIPA:  IN std_logic_vector(1 downto 0);
      DIPB:  IN std_logic_vector(1 downto 0);
      WEA:   IN std_logic;
      WEB:   IN std_logic;
      CLKA:  IN std_logic;
      CLKB:  IN std_logic;
      SSRA:  IN std_logic;
      SSRB:  IN std_logic;
      ENA:   IN std_logic;
      ENB:   IN std_logic;
      DOA:   OUT std_logic_vector(15 downto 0);
      DOB:   OUT std_logic_vector(15 downto 0);
      DOPA:  OUT std_logic_vector(1 downto 0);
      DOPB:  OUT std_logic_vector(1 downto 0));
END component;

begin

block_ram: RAMB16_S18_S18 port map(
      ADDRA => addra_i,
      ADDRB => ADDRB,
      DIA   => HFE_DOUT,
      DIB   => DIB,
      DIPA  => gnd_bus(1 downto 0),
      DIPB  => gnd_bus(1 downto 0),
      WEA   => write_i,
      WEB   => web,
      CLKA  => HFE_CLK,
      CLKB  => LB_CLK,
      SSRA  => gnd,
      SSRB  => gnd,
      ENA   => pwr,
      ENB   => enb,
      DOA   => open,
      DOB   => DOB,
      DOPA  => open,
      DOPB  => open
);


gnd_bus <= "00000000000000000000000000000000";
gnd <= '0';
pwr <= '1';

lup_block <= ADDRB(9 downto 6);

addra_i <= hfe_block & HFE_ADDR;
write_i   <= HFE_WEN and hfe_allocated;

hfe_communication:process(HFE_CLK, RESET)
begin
   --HFE_RDY   <= '0';
   if RESET = '1' then
      HFE_RDY          <= '0';
      hfe_allocated    <= '0';
      hfe_is_producing <= '0';
      hfe_block        <= "0000";
      hfe_block_aux    <= "0000";
      uh_valid         <= '0';
   elsif HFE_CLK'event and HFE_CLK = '1' then
      uh_valid  <= '0';
      HFE_RDY   <= '0';
      if HFE_REQ='1' then
         if hfe_is_producing='1' then
            uh_valid         <= '1';
            hfe_block        <= hfe_block+1;
            hfe_is_producing <= '0';
            hfe_allocated    <= '0';
         elsif ready(conv_integer(unsigned(hfe_block)))='0' then
            HFE_RDY       <= '1';
            hfe_allocated <= '1';
            hfe_block_aux <= hfe_block;
         end if;
      elsif hfe_allocated='1' then
         hfe_is_producing<='1';
      end if;
   end if;
end process;


--lup communication:
LUP_SR_VALID <= ready(conv_integer(unsigned(lup_block)));--OK
lup_communication:process(RESET,LUP_CLK,LUP_SR_CLEAN,ready)
begin
   if reset = '1' then
      uh_clean<='0';
   elsif LUP_CLK'event and LUP_CLK = '1' then
      uh_clean<='0';
      if LUP_SR_CLEAN='1' and ready(conv_integer(unsigned(lup_block)))='1' then
         uh_clean<='1';
      end if;
   end if;
end process;


ready_bits_handling:process(uh_valid,uh_clean,reset)
begin
   if reset='1' then
      ready <= "0000000000000000";
   else
      if uh_valid='1' then
         ready(conv_integer(unsigned(hfe_block_aux)))<='1';
      end if;
      if uh_clean='1' then
         ready(conv_integer(unsigned(lup_block)))<='0';
      end if;
   end if;
end process;

-- assert alive ready
-- assert globally if (ready(conv_integer(unsigned(lup_block)))) then
-- ((hfe_block <> lup_block) or (not write_i))
end debug;
