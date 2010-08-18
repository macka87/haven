
-- ibuf_test.vhd: Test entity for IBUF 
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
-- Address space:
-- --------------
-- 0000: Read from FIFO
-- 0004: Read/Reset reg_fifo_full register
-- 0008: Read/Set reg_ctrl register

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity ibuf_test is
   generic(
      ADDR_BASE   : integer;
      DATA_PATHS  : integer;     -- Output data width in bytes
      FIFO_SIZE   : integer      -- Packet fifo size
   );

   port (
      RESET    : in std_logic;

      DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : in std_logic;
      SOF_N      : in std_logic;
      SOP_N      : in std_logic;
      EOF_N      : in std_logic;
      EOP_N      : in std_logic;
      DST_RDY_N  : out std_logic;

      -- PACODAG interface
      CTRL_CLK    : in   std_logic;
      CTRL_DI        : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : out std_logic;
      CTRL_SOP_N     : out std_logic;
      CTRL_EOP_N     : out std_logic;
      CTRL_DST_RDY_N : in std_logic;
      CTRL_HDR_EN : out std_logic; -- Enables Packet Headers
      CTRL_FTR_EN : out std_logic; -- Enables Packet Footers

      -- IBUF status interface
      SOP         : in   std_logic;

      -- Sampling unit interface
      SAU_ACCEPT : out    std_logic;
      SAU_DV     : out    std_logic;

      -- ------------------------------------------------
      -- ---------- Internal bus signals ----------------
      LBCLK	     : in    std_logic;
      LBFRAME	     : in    std_logic;
      LBHOLDA	     : out   std_logic;
      LBAD	     : inout std_logic_vector(15 downto 0);
      LBAS	     : in    std_logic;
      LBRW	     : in    std_logic;
      LBRDY	     : out   std_logic;
      LBLAST	     : in    std_logic
   );
end ibuf_test;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of ibuf_test is

   signal lb_en          : std_logic;
   signal lb_rw          : std_logic;
   signal lb_addr        : std_logic_vector(2 downto 0);
   signal lb_di          : std_logic_vector(15 downto 0);
   signal lb_do          : std_logic_vector(15 downto 0);
   signal lb_drdy        : std_logic;
   signal lb_ardy        : std_logic;

   signal fifo_rd       : std_logic;
   signal fifo_wr       : std_logic;
   signal fifo_di       : std_logic_vector(35 downto 0);
   signal fifo_do       : std_logic_vector(35 downto 0);
   signal fifo_dv       : std_logic;
   signal fifo_full     : std_logic;

   signal reg_fifo_full : std_logic;
   signal fifo_full_rst : std_logic;
   signal reg_adc_drdy : std_logic;

   -- Control register
   -- bit 0: 0 - DST_RDY_N is still asserted (tied to zero) 
   --        1 - enable DST_RDY_N deassertion when IBUF_TEST fifo is full
   signal reg_ctrl      : std_logic_vector(7 downto 0);
   signal reg_ctrl_we   : std_logic;

   -- Status register
   signal reg_status    : std_logic_vector(7 downto 0);
   signal reg_status_rst: std_logic;

   signal adc_rd        : std_logic;
   signal adc_rd_i      : std_logic;
   signal adc_wr        : std_logic;
   signal adc_addr      : std_logic_vector(1 downto 0);
   signal adc_di        : std_logic_vector(31 downto 0);
   signal adc_do        : std_logic_vector(31 downto 0);
   signal adc_drdy      : std_logic;
   signal adc_drdy_i    : std_logic;

   -- SAU signals
   signal reg_sop1 : std_logic;
   signal reg_sop2 : std_logic;
   signal cnt_sau : std_logic_vector(1 downto 0);
   signal cnt_sau_ovf : std_logic;

begin

-- LBCONN_MEM instantination --------------------------------------------------
LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   BASE           => ADDR_BASE,  -- base address
   ADDR_WIDTH     => 3 -- address bus width
)
port map(
   DATA_OUT => lb_di,
   DATA_IN  => lb_do,
   ADDR     => lb_addr,
   EN       => lb_en,
   RW       => lb_rw,
   SEL      => open,
   DRDY     => lb_drdy,
   ARDY     => '1',

   RESET    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

ADC2LB_U: entity work.adc2lb
   generic map(
      ADDR_WIDTH  => 3,
      FREQUENCY   => 100
   )
   port map(
      RESET       => RESET,

      -- Address decoder interface
      CLK         => LBCLK,
      ADC_RD      => adc_rd,
      ADC_WR      => adc_wr,
      ADC_ADDR    => adc_addr,
      ADC_DI      => adc_di,
      ADC_DO      => adc_do,
      ADC_DRDY    => adc_drdy,

      -- Local Bus interface
      LBCLK       => LBCLK,
      LB_EN       => lb_en,
      LB_RW       => lb_rw,
      LB_ADDR     => lb_addr,
      LB_DI       => lb_di,
      LB_DO       => lb_do,
      LB_DRDY     => lb_drdy
   );

FIFO_BRAM_U: entity work.fifo_bram
   generic map(
      -- ITEMS = Numer of items in FIFO
      ITEMS       => FIFO_SIZE,
      
      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      BRAM_TYPE   => 36,

      -- Data Width, DATA_WIDTH mod BRAM_TYPE must be 0
      DATA_WIDTH  =>  36
   )
   port map(
      CLK      => LBCLK,
      RESET    => RESET,

      -- Write interface
      WR       => fifo_wr,
      DI       => fifo_di,
      FULL     => fifo_full,
      LSTBLK   => open,

      -- Read interface
      RD       => fifo_rd,
      DO       => fifo_do,
      DV       => fifo_dv,
      EMPTY    => open
   );

-- -------------------------------------------------------------
-- Address Decoder
process(adc_addr, reg_fifo_full,fifo_do,fifo_dv, reg_adc_drdy, adc_wr,
adc_rd,reg_ctrl, reg_status, adc_rd_i)
begin
   adc_do <= (others => '0');
   adc_drdy <= '0';
   fifo_rd <= '0';
   fifo_full_rst <= '0';
   reg_ctrl_we <= '0';
   reg_status_rst <= '0';
   
   case (adc_addr(1 downto 0)) is 
      -- - - - - - - - - - - - - - - - - - - - -
      -- Read data from FIFO
      when "00" =>
         fifo_rd <= adc_rd_i;
         adc_drdy <= reg_adc_drdy;
         adc_do <= fifo_do(31 downto 0);
      -- - - - - - - - - - - - - - - - - - - - -
      -- Operate reg_fifo_full_rst register
      when "01" =>
         adc_drdy <= reg_adc_drdy;
         adc_do(0) <= reg_fifo_full;
         fifo_full_rst <= adc_wr;
      -- - - - - - - - - - - - - - - - - - - - -
      -- IBUF TEST control register
      when "10" =>
         adc_drdy <= reg_adc_drdy;
         adc_do(7 downto 0) <= reg_ctrl;
         reg_ctrl_we <= adc_wr;
      -- - - - - - - - - - - - - - - - - - - - -
      -- IBUF TEST status register
      when "11" =>
         adc_drdy <= reg_adc_drdy;
         adc_do(7 downto 0) <= reg_status;
         reg_status_rst <= adc_wr;
      -- - - - - - - - - - - - - - - - - - - - -
      when others =>
         null;
   end case;
end process;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_ctrl <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (reg_ctrl_we = '1') then
         reg_ctrl <= adc_di(7 downto 0);
      end if;
   end if;
end process;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_status <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (reg_status_rst = '1') then
         reg_status <= (others => '0');
      else
         if (EOF_N = '0') then
            reg_status(0) <= '1';
         end if;
         if (EOP_N = '0') then
            reg_status(1) <= '1';
         end if;
         if (SOF_N = '0') then
            reg_status(2) <= '1';
         end if;
         if (SOP_N = '0') then
            reg_status(3) <= '1';
         end if;
      end if;
   end if;
end process;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_fifo_full <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      if (fifo_full_rst = '1') then
         reg_fifo_full <= '0';
      elsif (fifo_full = '1') then
         reg_fifo_full <= '1';
      end if;
   end if;
end process;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      adc_drdy_i <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      adc_drdy_i <= adc_rd;
   end if;
end process;
   
-- to avoid false reading due to adc_rd exccesive assertion
adc_rd_i <= adc_rd and not adc_drdy_i;
   
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_adc_drdy <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_adc_drdy <= adc_rd and not adc_drdy_i;
   end if;
end process;
   
fifo_wr <= not SRC_RDY_N;
fifo_di(20 downto 0) <= DREM(0) & SOP_N & SOF_N & EOP_N & EOF_N & DATA(15 downto 0);
fifo_di(35 downto 21) <= (others => '0');
DST_RDY_N <= reg_fifo_full when reg_ctrl(0) = '1' else
             '0';


-- PACODAG
CTRL_DI     <= (others => '0');
CTRL_SRC_RDY_N <= '1';
CTRL_REM    <= (others => '0');
CTRL_SOP_N  <= '1';
CTRL_EOP_N  <= '1';
CTRL_HDR_EN <= '0';
CTRL_FTR_EN <= '0';

-- Sampling Unit
process(RESET, CTRL_CLK)
begin
   if (RESET = '1') then
      reg_sop1 <= '0';
      reg_sop2 <= '0';
   elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
      reg_sop1 <= SOP;
      reg_sop2 <= reg_sop1;
   end if;
end process;

process(RESET, CTRL_CLK)
begin
   if (RESET = '1') then
      cnt_sau <= (others => '0');
   elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
      if (SOP='1') then
         cnt_sau <= cnt_sau + 1;
      end if;
   end if;
end process;

cnt_sau_ovf <= '1' when cnt_sau = "11" else
               '0';

SAU_DV <= reg_sop2;
SAU_ACCEPT <= cnt_sau_ovf;

end behavioral;




