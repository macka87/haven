-- i2c.vhd - I2C top_level
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--
-- control reg
-- -------------------------------------
-- | dev RW |  addr  |xxxxxxxx| data_in|
-- -------------------------------------
-- device address is 7bit, 0bit is RW (1 - read, 0 - write)

-- status reg
-- -------------------------------------
-- |SBxxxxxx|xxxxxxxx|xxxxxxxx|data_out|
-- -------------------------------------
-- S - status (1 - OK, 0 - false)
-- B - busy   (1 - busy, 0 - not busy)


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- -------------------------------------------------------
--                 Entity declaration
-- -------------------------------------------------------
entity i2c is
   generic(
      BASE_ADDR  : integer   -- base address 
      --FREQUENCY  : string     -- frequency
   );
   port (
      RESET   : in    std_logic;
      CLK     : in    std_logic; -- 100MHz

      -- LB signals
      LBCLK   : in    std_logic; 
      LBFRAME : in    std_logic; -- Frame
      LBHOLDA : out   std_logic; -- Hold Ack (HOLDA), active LOW
      LBAD    : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS    : in    std_logic; -- Adress strobe
      LBRW    : in    std_logic;
      LBRDY   : out   std_logic; -- Ready, active LOW
      LBLAST  : in    std_logic;

      -- I2C interface
      SCL_O   : out std_logic;
      SCL_I   : in  std_logic;
      SDA_O   : out std_logic;
      SDA_I   : in  std_logic
   );
end i2c;
-------------------------------------------------------------------------------

architecture full of i2c is
   signal reg_ctrl: std_logic_vector(31 downto 0);
   signal reg_status: std_logic_vector(31 downto 0);
   signal i2c_master_do: std_logic_vector(7 downto 0);
   signal i2c_master_en: std_logic;
   signal i2c_master_ok: std_logic;
   signal i2c_master_done: std_logic;
   signal i2c_master_busy: std_logic;
   signal i2c_master_state: std_logic_vector(1 downto 0);
   signal cs_reg_ctrl: std_logic;
   signal cs_reg_status: std_logic;

   signal adc_rd: std_logic;
   signal adc_wr: std_logic;
   signal adc_addr: std_logic_vector(2 downto 0);
   signal adc_di: std_logic_vector(31 downto 0);
   signal adc_do: std_logic_vector(31 downto 0);   
   signal adc_drdy: std_logic;


begin
  
   -- I2C_MASTER instantination -----------------------------------------------
   I2C_MASTER_U : entity work.i2c_master
   port map (
      RESET   => RESET,
      CLK     => CLK,
      
      DEV     => reg_ctrl(31 downto 25),
      ADDR    => reg_ctrl(23 downto 16),
      RW      => reg_ctrl(24),
      EN      => i2c_master_en,
      DI      => reg_ctrl(7 downto 0),
      
      DO      => i2c_master_do,
      OP_OK   => i2c_master_ok,
      OP_DONE => i2c_master_done,
      BUSY    => i2c_master_busy,
      STATE   => i2c_master_state,
      
      SCL_O   => SCL_O,
      SCL_I   => SCL_I,
      SDA_O   => SDA_O,
      SDA_I   => SDA_I
   );

   -- lb_conn_reg instantination ----------------------------------------------
   LB_CONNECT_U : entity work.lb_connect
   generic map (
      BASE_ADDR  => BASE_ADDR,
      ADDR_WIDTH => 3,
      FREQUENCY  => 100
   )
   port map (
      RESET    => RESET,

      LBCLK    => LBCLK,      
      LBFRAME  => LBFRAME,
      LBHOLDA  => LBHOLDA,
      LBAD     => LBAD,
      LBAS     => LBAS,
      LBRW     => LBRW,
      LBRDY    => LBRDY,
      LBLAST   => LBLAST,
      
      -- address decoder ------------------------------------------------------
      CLK      => CLK,
      ADC_RD   => adc_rd,
      ADC_WR   => adc_wr,
      ADC_ADDR => adc_addr,
      ADC_DI   => adc_di,
      ADC_DO   => adc_do,   
      ADC_DRDY => adc_drdy
   );

   cs_reg_ctrl   <= '1' when (ADC_ADDR="000") else '0';
   cs_reg_status <= '1' when (ADC_ADDR="100") else '0';

   adc_do <= reg_ctrl   when (cs_reg_ctrl='1')   else
             reg_status when (cs_reg_status='1') else
	     (others=>'0');

   reg_ctrl_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_ctrl      <= (others=>'0');
         i2c_master_en <= '0';
      elsif (CLK'event and CLK='1') then
         if (cs_reg_ctrl='1' and adc_wr='1') then
            reg_ctrl      <= adc_di;
            i2c_master_en <= '1';
         else
            i2c_master_en <= '0';
         end if;
      end if;
   end process;

   reg_status_p: process(RESET, CLK)
   begin
      if (RESET='1') then
         reg_status <= (others=>'0');
      elsif (CLK'event and CLK='1') then
         adc_drdy <= adc_rd; -- adc_drdy is delayed adc_rd
         reg_status(30) <= i2c_master_busy;
         if (i2c_master_done='1') then
            reg_status(31) <= i2c_master_ok;
            reg_status(9 downto 8) <= i2c_master_state;
            reg_status(7 downto 0) <= i2c_master_do;
         end if;
      end if;
   end process;

end full;
