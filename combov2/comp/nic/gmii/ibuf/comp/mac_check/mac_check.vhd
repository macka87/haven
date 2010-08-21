
-- mac_check.vhd: MAC address checking unit 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity mac_check is
   generic (
      MACS  : integer := 16   -- Number of MACs to compare
   );
   port (
      -- Common Input
      RESET    : in std_logic;
      CLK      : in std_logic;
      EN       : in std_logic;   -- IBUF enable bit. MAC Memory cannot be accessed by PCI when asserted.

      -- MAC address input
      MAC_IN   : in std_logic_vector(47 downto 0);
      CHECK    : in std_logic;

      -- Result output
      CHECK_FIN   : out std_logic;
      MAC_MATCH   : out std_logic;
      MULTICAST   : out std_logic;
      BROADCAST   : out std_logic;

      -- Address decoder interface
      ADC_CLK     : in  std_logic;
      ADC_RD      : in  std_logic; -- Read Request
      ADC_WR      : in  std_logic; -- Write Request
      ADC_ADDR    : in  std_logic_vector(log2(MACS) downto 0);  -- Address
      ADC_DI      : in  std_logic_vector(31 downto 0);  -- Input Data
      ADC_DO      : out std_logic_vector(31 downto 0);  -- Output Data
      ADC_DRDY    : out std_logic
   );
end mac_check;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of mac_check is

component SP_DISTMEM is
   generic(
      -- Data Width
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE : integer := 16;
      -- debug prints
      DEBUG   : boolean := false
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (LOG2(ITEMS)-1 downto 0);
      DO     : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
end component SP_DISTMEM;

   signal reg_adc_drdy : std_logic;
   signal cnt_macmem_addr : std_logic_vector(log2(MACS)-1 downto 0);
   signal macmem_addr : std_logic_vector(log2(MACS)-1 downto 0);
   signal reg_check : std_logic;
   signal reg_check_rst : std_logic;
   signal reg_check_set : std_logic;
   signal reg_mac_match : std_logic;
   signal reg_mac_match_rst : std_logic;
   signal reg_mac_match_set : std_logic;
   signal reg_macmem_item : std_logic_vector(31 downto 0);
   signal reg_macmem_item_we : std_logic;
   signal reg_adc_addr : std_logic_vector(log2(MACS) downto 0);
   signal macmem_di : std_logic_vector(48 downto 0);
   signal macmem_wr : std_logic;
   signal macmem_do : std_logic_vector(48 downto 0);
   signal cmp_cnt_macmem_addr : std_logic;
   signal cmp_mac_match : std_logic;
   signal reg_broadcast_rst : std_logic;
   signal reg_broadcast_set : std_logic;
   signal reg_multicast_rst : std_logic;
   signal reg_multicast_set : std_logic;
   signal cmp_broadcast : std_logic;
   signal cmp_multicast : std_logic;
   signal reg_broadcast : std_logic;
   signal reg_multicast : std_logic;

begin

-- -------------------------------------------------------------
-- Address decoder

macmem_addr <= cnt_macmem_addr when EN = '1' else
               ADC_ADDR(log2(MACS) downto 1);

process(RESET, ADC_CLK)
begin
   if (RESET = '1') then
      reg_macmem_item <= (others => '0');
   elsif (ADC_CLK'event AND ADC_CLK = '1') then
      if (reg_macmem_item_we = '1') then
         reg_macmem_item <= ADC_DI;
      end if;
   end if;
end process;

process(RESET, ADC_CLK)
begin
   if (RESET = '1') then
      reg_adc_drdy <= '0';
   elsif (ADC_CLK'event AND ADC_CLK = '1') then
      reg_adc_drdy <= ADC_RD;
   end if;
end process;
ADC_DRDY <= reg_adc_drdy;

process(RESET, ADC_CLK)
begin
   if (RESET = '1') then
      reg_adc_addr <= (others => '0');
   elsif (ADC_CLK'event AND ADC_CLK = '1') then
      reg_adc_addr <= ADC_ADDR(log2(MACS) downto 0);
   end if;
end process;

macmem_di(31 downto 0) <= reg_macmem_item;
macmem_di(48 downto 32) <= ADC_DI(16 downto 0);

reg_macmem_item_we <= (not ADC_ADDR(0)) and ADC_WR;
macmem_wr <= ADC_ADDR(0) and ADC_WR;

ADC_DO <= "000" & x"000" & macmem_do(48 downto 32) when reg_adc_addr(0) = '1' else
          macmem_do(31 downto 0);

-- -------------------------------------------------------------
-- MAC memory
-- Can be updated when EN is deasserted only.

macmem_u: SP_DISTMEM
   generic map(
      -- Data Width
      DATA_WIDTH  => 49, -- MAC address + flag
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS => MACS,
      -- debug prints
      DEBUG   => false
   )
   port map(
      -- Common interface
      RESET  => RESET,
      -- R/W Port
      DI     => macmem_di,
      WE     => macmem_wr,
      WCLK   => CLK,
      ADDR   => macmem_addr,
      DO     => macmem_do
      );


-- -------------------------------------------------------------
-- Control Unit

process(RESET, CLK)
begin
   if (RESET = '1') then
      cnt_macmem_addr <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (cmp_cnt_macmem_addr = '1') then
         cnt_macmem_addr <= (others => '0');
      elsif (reg_check = '1') then
         cnt_macmem_addr <= cnt_macmem_addr + 1;
      end if;
   end if;
end process;

cmp_cnt_macmem_addr <= '1' when cnt_macmem_addr = conv_std_logic_vector(MACS-1,log2(MACS)) else
                       '0';

reg_check_rst <= cmp_cnt_macmem_addr;
reg_check_set <= CHECK;
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_check <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reg_check_rst = '1') then
         reg_check <= '0';
      elsif (reg_check_set = '1') then
         reg_check <= '1';
      end if;
   end if;
end process;

CHECK_FIN <= cmp_cnt_macmem_addr;

reg_mac_match_rst <= CHECK;
reg_mac_match_set <= cmp_mac_match;
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_mac_match <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reg_mac_match_rst = '1') then
         reg_mac_match <= '0';
      elsif (reg_mac_match_set = '1') then
         reg_mac_match <= '1';
      end if;
   end if;
end process;

MAC_MATCH <= reg_mac_match;

reg_broadcast_rst <= CHECK;
reg_broadcast_set <= cmp_broadcast;
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_broadcast <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reg_broadcast_rst = '1') then
         reg_broadcast <= '0';
      elsif (reg_broadcast_set = '1') then
         reg_broadcast <= '1';
      end if;
   end if;
end process;

BROADCAST <= reg_broadcast;

reg_multicast_rst <= CHECK;
reg_multicast_set <= cmp_multicast;
process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_multicast <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (reg_multicast_rst = '1') then
         reg_multicast <= '0';
      elsif (reg_multicast_set = '1') then
         reg_multicast <= '1';
      end if;
   end if;
end process;

MULTICAST <= reg_multicast;

-- -------------------------------------------------------------
-- Comparators

cmp_mac_match <= '1' when ((macmem_do(47 downto 0) = MAC_IN) and (macmem_do(48) = '1')) else
                 '0';
cmp_broadcast <= '1' when (MAC_IN =  x"FFFFFFFFFFFF") else
                 '0';
cmp_multicast <= '1' when (MAC_IN(40) = '1') else
                 '0';

end behavioral;


