-- uh_fifo.vhd: Unified Header FIFO, full implementation of a single UH FIFO
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Filip Hofer    <fil@liberouter.org>
--            Tomas Martinek <martinek@liberouter.org>
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

-- ----------------------------------------------------------------------
--  Architecture declaration: full
-- ----------------------------------------------------------------------

architecture full of UH_FIFO is
-- ---------------------- BlockRAM component ----------------------------
component RAMB16_S18_S36
   port (
      ADDRA: IN std_logic_vector(9 downto 0);
      ADDRB: IN std_logic_vector(8 downto 0);
      DIA:   IN std_logic_vector(15 downto 0);
      DIB:   IN std_logic_vector(31 downto 0);
      DIPA:  IN std_logic_vector(1 downto 0);
      DIPB:  IN std_logic_vector(3 downto 0);
      WEA:   IN std_logic;
      WEB:   IN std_logic;
      CLKA:  IN std_logic;
      CLKB:  IN std_logic;
      SSRA:  IN std_logic;
      SSRB:  IN std_logic;
      ENA:   IN std_logic;
      ENB:   IN std_logic;
      DOA:   OUT std_logic_vector(15 downto 0);
      DOB:   OUT std_logic_vector(31 downto 0);
      DOPA:  OUT std_logic_vector(1 downto 0);
      DOPB:  OUT std_logic_vector(3 downto 0));
end component;

-- --------------------- Dual port flags component -----------------------
component DP_REGFLAGS
   generic(
      EXADDR   : integer
   );
	port(
      RESET    : in  std_logic;
      -- SET part
      CLK_SET  : in  std_logic;
      SET      : in  std_logic;
      ADDR_SET : in  std_logic_vector(EXADDR-1 downto 0);
      DO_SET   : out std_logic;
      -- CLR part
      CLK_CLR  : in  std_logic;
      CLR      : in  std_logic;
      ADDR_CLR : in  std_logic_vector(EXADDR-1 downto 0);
      DO_CLR   : out std_logic;

      DO_ALL   : out std_logic_vector((2**EXADDR)-1 downto 0)
	);
end component;

-- --------------------- Signals declaration -----------------------
signal hfe_block        : std_logic_vector(3 downto 0);
signal hfe_block_aux    : std_logic_vector(3 downto 0);
signal ready            : std_logic_vector(15 downto 0);
signal reg_ready        : std_logic_vector(15 downto 0);
signal hfe_allocated    : std_logic;
signal addra_i          : std_logic_vector(9 downto 0);
signal mx_lup_addr      : std_logic_vector(8 downto 0);
signal write_i          : std_logic;
signal uh_valid         : std_logic;
signal hfe_is_producing : std_logic;
signal hfe_rdy_i        : std_logic;

signal lup_block        : std_logic_vector(3 downto 0);
signal lup_data_int     : std_logic_vector(31 downto 0);
signal lup_sr_valid_int : std_logic;
signal bram_enb         : std_logic;
signal reg_lup_sr_valid : std_logic;
signal reg_lup_ready    : std_logic_vector(15 downto 0);

--  Predefined signals
signal gnd_bus          : std_logic_vector(31 downto 0);
signal gnd              : std_logic;
signal pwr              : std_logic;

-- HFE and LUP couter - pointers to UH
signal cnt_hferec       : std_logic_vector(31 downto 0);
signal cnt_hferec_ce    : std_logic;
signal cnt_luprec       : std_logic_vector(31 downto 0);
signal cnt_luprec_ce    : std_logic;

-- address decoder signals
signal reg_adc_addr     : std_logic_vector(9 downto 0);
signal reg_adc_do       : std_logic_vector(31 downto 0);
signal mx_adc_do        : std_logic_vector(31 downto 0);

begin

--  Predefined signals - zero and ones
gnd_bus <= (others => '0');
gnd <= '0';
pwr <= '1';

-- -------------------------------------------------------------------
--                  Address decoder part
-- -------------------------------------------------------------------

-- reg_adc_flags register
process(RESET, LUP_CLK)
begin
   if (RESET = '1') then
      reg_adc_addr   <= (others => '0');
      reg_adc_do     <= (others => '0');
   elsif (LUP_CLK'event AND LUP_CLK = '1') then
      reg_adc_addr   <= ADC_ADDR;
      reg_adc_do     <= mx_adc_do;
   end if;
end process;

-- output data multiplexor
with ADC_ADDR(1 downto 0) select
mx_adc_do <= cnt_hferec       when "00",
             cnt_luprec       when "01",
             gnd_bus(15 downto 0) &
             reg_ready        when "10",
             (others => '0')  when others;

-- output data multiplexor
with reg_adc_addr(9) select
ADC_DO <= lup_data_int     when '0',
          reg_adc_do       when '1',
          (others => '0')  when others;

-- -------------------------------------------------------------------
--                            UH part
-- -------------------------------------------------------------------

-- cnt_hferec counter
cnt_hferec_ce <= uh_valid;
process(RESET, HFE_CLK)
begin
   if (RESET = '1') then
      cnt_hferec <= (others => '0');
   elsif (HFE_CLK'event AND HFE_CLK = '1') then
      if (cnt_hferec_ce = '1') then
         cnt_hferec <= cnt_hferec + 1;
      end if;
   end if;
end process;

-- cnt_luprec counter
cnt_luprec_ce <= LUP_SR_CLEAN;
process(RESET, LUP_CLK)
begin
   if (RESET = '1') then
      cnt_luprec <= (others => '0');
   elsif (LUP_CLK'event AND LUP_CLK = '1') then
      if (cnt_luprec_ce = '1') then
         cnt_luprec <= cnt_luprec + 1;
      end if;
   end if;
end process;


lup_block <= LUP_ADDR(8 downto 5);

addra_i <= hfe_block & HFE_ADDR;
write_i <= HFE_WEN and hfe_allocated;

HFE_RDY <= hfe_rdy_i;

hfe_communication:process(HFE_CLK, RESET)
begin
   if reset = '1' then
      hfe_rdy_i        <= '0';
      hfe_allocated    <= '0';
      hfe_is_producing <= '0';
      hfe_block        <= "0000";
      hfe_block_aux    <= "0000";
      uh_valid         <= '0';
   elsif HFE_CLK'event and HFE_CLK = '1' then
      uh_valid  <= '0';
      hfe_rdy_i <= '0';
      if HFE_REQ='1' then
         if hfe_is_producing='1' then
            uh_valid         <= '1';
            hfe_block        <= hfe_block+1;
            hfe_is_producing <= '0';
            hfe_allocated    <= '0';
         elsif reg_ready(conv_integer(unsigned(hfe_block)))='0' then
            hfe_rdy_i     <= '1';
            hfe_allocated <= '1';
            hfe_block_aux <= hfe_block;
         end if;
      elsif hfe_allocated='1' then
         hfe_is_producing<='1';
      end if;
   end if;
end process;

-- Ready to store informations to UH
reg_ready_proc: process(HFE_CLK,RESET)
begin
   if reset='1' then
      reg_ready <= (others => '0');
   elsif HFE_CLK'event and HFE_CLK='1' then
      reg_ready <= ready;
   end if;
end process;


-- mx_lup_addr multiplexor
mx_lup_addr <= LUP_ADDR when (ADC_RD = '0') else
               ADC_ADDR(8 downto 0);

-- BRAM instantion
bram_enb <= lup_sr_valid_int or ADC_RD;

block_ram: RAMB16_S18_S36 port map(
      CLKA  => HFE_CLK,
      ENA   => write_i,
      WEA   => write_i,
      ADDRA => addra_i,
      DIA   => HFE_DOUT,
      DIPA  => gnd_bus(1 downto 0),
      DOA   => open,
      DOPA  => open,
      SSRA  => gnd,

      CLKB  => LUP_CLK,
      ENB   => bram_enb,
      WEB   => gnd,
      ADDRB => mx_lup_addr,
      DIB   => gnd_bus,
      DIPB  => gnd_bus(3 downto 0),
      DOB   => lup_data_int,
      DOPB  => open,
      SSRB  => gnd
);


-- dp_reg_flags instantion
flags: dp_regflags
generic map(
   EXADDR => 4
)
port map(
   RESET       => RESET,
   -- SET part
   CLK_SET     => HFE_CLK,
   SET         => uh_valid,
   ADDR_SET    => hfe_block_aux,
   DO_SET      => open,
   -- CLR part
   CLK_CLR     => LUP_CLK,
   CLR         => LUP_SR_CLEAN,
   ADDR_CLR    => lup_block,
   DO_CLR      => open,
   -- Output
   DO_ALL      => ready
);


-- lup_sr_valid multiplexor
with lup_block select
lup_sr_valid_int <= reg_lup_ready(0)  when X"0",
                    reg_lup_ready(1)  when X"1",
                    reg_lup_ready(2)  when X"2",
                    reg_lup_ready(3)  when X"3",
                    reg_lup_ready(4)  when X"4",
                    reg_lup_ready(5)  when X"5",
                    reg_lup_ready(6)  when X"6",
                    reg_lup_ready(7)  when X"7",
                    reg_lup_ready(8)  when X"8",
                    reg_lup_ready(9)  when X"9",
                    reg_lup_ready(10) when X"a",
                    reg_lup_ready(11) when X"b",
                    reg_lup_ready(12) when X"c",
                    reg_lup_ready(13) when X"d",
                    reg_lup_ready(14) when X"e",
                    reg_lup_ready(15) when X"f",
                    '0'           when others;


-- reg_lup_sr_valid register
process(RESET, LUP_CLK)
begin
   if (RESET = '1') then
      reg_lup_sr_valid  <= '0';
      reg_lup_ready     <= (others => '0');
   elsif (LUP_CLK'event AND LUP_CLK = '1') then
      reg_lup_sr_valid  <= lup_sr_valid_int;
      reg_lup_ready     <= ready;
   end if;
end process;

-- -------------------------------------------------------------------
--                        Interface Mapping
-- -------------------------------------------------------------------
LUP_DATA       <= lup_data_int;
LUP_SR_VALID   <= reg_lup_sr_valid;

-- -------------------------------------------------------------------
end full;

