-- sysctrl.vhd : ComboV2 PCI system control (card ID, reconfiguration, etc.)
-- Copyright (C) 2008 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
-- BAR0 address space
-- 0x0000: Design ID & revision
-- 0x0004: Design build time
-- 0x0010: System control register (SYSCTRL)
-- bit 0     - System reset
--     15:1  - reserved
--     19:16 - FPGA boot design revision select (0..15), default 0 
--     20    - FPGA boot source for reconfiguration (0 = PSRAM, 1 = FLASH)
--     21    - reconfiguration status: '1' = reconfiguration in progress
--     22    - reconfiguration error: '1' = last reconfiguration atempt was not successful
--     29:23 - reserved
--     30    - immediate start of the reconfiguration (no delay)
--     31    - start of delayed reconfiguration (delay time is defined by the reconfig delay counter)
-- 0x0014: Reconfiguration timeout (RCFGTO) in number of 125MHz clocks
-- 0x0018: Switch status (23..16), interface 2 status (15..8) & Interface 1 status (bits 7..0)
-- 0x001C: PLL synthesiser M (5..0), N (9..8), select (15)
-- 0x0020: I2C controller for the AT88SC0104 security chip
-- 0x0028: Reserved for one-wire interface to the ID chip
-- 0x0030: I2C controller for interface 1
-- 0x0038: I2C controller for interface 2
-- 0x0100: FLASH/PSRAM command/address register, read: bit 0 = FLASH ready for new data (rdy), bit 1 = BUSY (not IDLE)
-- 0x0104: MB data write mailbox
-- 0x0108: MB data read mailbox
-- 0x0200: Interface 2 boot control
--   bit 0: '1' - enable boot operation (write-only)
--   bit 1: '1' - ready for boot data (read-only)
-- 0x0204: Interface 1 boot data (32bit, write-only)
-- 0x0208: Interface 2 boot control
--   bit 0: '1' - enable boot operation (write-only)
--   bit 1: '1' - ready for boot data (read-only)
-- 0x020C: Interface 2 boot data (32bit, write-only)

-- I2C controllers:
-- bits  7...0 PRERlo
--      15...8 PRERhi
--      23..16 CTR - Control register
--      31..24 reserved
-- (Address BASE+0x04)
--      39..32 CR - Command register
--      47..40 TXR/RXR
--      others reserved
-- Interface status registers
-- bit 0 : '0' = interface present, '1' = interface not present
--     1 : '0' = JTAG chain present, '1' = not present (valid only when bit 0 is set)
--     2 : boot status (reserved)

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use work.ib_pkg.all;

library UNISIM;
use UNISIM.vcomponents.all;

-- ----------------------------------------------------------------------------
--                    Architecture declaration                               --
-- ----------------------------------------------------------------------------

entity sysctrl_cv2 is
   generic (
      REVISION   : std_logic_vector(31 downto 0) := X"6d050103";
      BUILD_TIME : std_logic_vector(31 downto 0) := X"82140000"
   );   
   port (
      RESET      : in std_logic; -- Global async reset
      ICS_CLK    : in std_logic; -- Internal bus clock (250MHz max)
      CCLK       : in std_logic; -- Configuration interface clock (100MHz max)
      SW_RESET   : out std_logic;
      -- IB - write port 
      DWR        : in  std_logic_vector(63 downto 0);
      DWR_BE     : in  std_logic_vector( 7 downto 0);
      WEN        : in  std_logic;
      WR_ADDR    : in  std_logic_vector(17 downto 0);
      WR_RDY     : out std_logic;
      -- IB - read port
      DRD        : out std_logic_vector(63 downto 0);
      DRD_VLD    : out std_logic;
      RD_ARDY    : out std_logic;
      DRD_RDY    : in  std_logic;
      RD_ADDR    : in std_logic_vector(17 downto 0);
      RD_REQ     : in  std_logic;
      -- Data/command FIFO interface
      MB_CMD     : out std_logic;
      MB_CMD_ACK : in  std_logic;
      MB_DWR     : out std_logic_vector(31 downto 0);
      MB_WEN     : out std_logic;
      MB_DRD     : in  std_logic_vector(31 downto 0);
      MB_RD_REQ  : out std_logic;
      MB_RD_ACK  : in  std_logic;
      MB_BUSY    : in  std_logic;
      MB_DRDY    : in  std_logic;
      -- 
      IF1BOOT_DATA : out std_logic_vector(31 downto 0);
      IF1BOOT_WEN  : out std_logic;
      IF1BOOT_PROG : out std_logic;
      IF1BOOT_RDY  : in  std_logic;
      --
      IF2BOOT_DATA : out std_logic_vector(31 downto 0);
      IF2BOOT_WEN  : out std_logic;
      IF2BOOT_PROG : out std_logic;
      IF2BOOT_RDY  : in  std_logic;
      -- System control ports
      RECONFIG   : out std_logic;     -- Active HIGH "reconfig" pulse 
      RECFG_REV  : out std_logic_vector(4 downto 0); -- Reconfig revision select (PSRAM or FLASH starting address)
      RECFG_ERR  : in  std_logic;
      --
      PLLM       : out std_logic_vector(5 downto 0);
      PLLN       : out std_logic_vector(1 downto 0);
      PLLOAD0_N  : out std_logic;
      PLLOAD1_N  : out std_logic;
      -- 
      CSDA       : inout std_logic;
      CSCL       : inout std_logic;
      IF1SDA     : inout std_logic;
      IF1SCLK    : inout std_logic;
      IF2SDA     : inout std_logic;
      IF2SCLK    : inout std_logic;
      IF1STAT    : in std_logic_vector(7 downto 0);
      IF2STAT    : in std_logic_vector(7 downto 0);
      SWITCH     : in std_logic_vector(7 downto 0)
   );
end sysctrl_cv2;

architecture structural of sysctrl_cv2 is

-- Resets & clocks
signal sw_reset_i   : std_logic;        -- Internal system reset
signal cntr         : std_logic_vector(25 downto 0);        -- ICS clock
-- PCI device configuration space & reconfiguration control
signal rcfg_start       : std_logic;
signal delay_cntr       : std_logic_vector(31 downto 0) := (others => '1');
signal delay_cntr_en    : std_logic;
signal reconfig_i       : std_logic := '0';
signal force_reconfig   : std_logic := '0';
signal reconfig_gclk0   : std_logic := '0';
signal reconfig_gclk    : std_logic := '0';
-- User application & internal bus signals
-- Control signals
signal drd_xfer   : std_logic;
signal reg_dwr    : std_logic_vector(DWR'high downto 0);
signal reg_dwr_be : std_logic_vector(DWR_BE'high downto 0);
signal reg_wen    : std_logic;
signal reg_wr_addr: std_logic_vector(WR_ADDR'high downto 0);

-- My registers
signal sysctrl_reg: std_logic_vector(63 downto 0);
signal rcfg_delay : std_logic_vector( 7 downto 0);
signal rev_sel    : std_logic_vector(4 downto 0);
signal recfg_err_reg : std_logic;

--
signal pulse_cntr  : std_logic_vector(3 downto 0);
signal icap_en     : std_logic;
signal reg_mb_dwr  : std_logic_vector(31 downto 0);
signal reg_mb_cmd  : std_logic;
signal reg_mb_wen  : std_logic;
-- I2C controllers
signal i2c_at_drd  : std_logic_vector(63 downto 0);
signal i2c_at_wen  : std_logic;
signal i2c_at_scl     : std_logic;
signal i2c_at_scl_oen : std_logic;
signal i2c_at_sda     : std_logic;
signal i2c_at_sda_oen : std_logic;

signal i2c_if1_drd  : std_logic_vector(63 downto 0);
signal i2c_if1_wen  : std_logic;
signal i2c_if1_scl     : std_logic;
signal i2c_if1_scl_oen : std_logic;
signal i2c_if1_sda     : std_logic;
signal i2c_if1_sda_oen : std_logic;

signal i2c_if2_drd  : std_logic_vector(63 downto 0);
signal i2c_if2_wen  : std_logic;
signal i2c_if2_scl     : std_logic;
signal i2c_if2_scl_oen : std_logic;
signal i2c_if2_sda     : std_logic;
signal i2c_if2_sda_oen : std_logic;
signal reg_pllm        : std_logic_vector(5 downto 0);
signal reg_plln        : std_logic_vector(1 downto 0);

  -- Write to a 64-bit register with byte enables ----------------------------
  function write64(reg : in std_logic_vector(63 downto 0); -- current value of the register
                   val : in std_logic_vector(63 downto 0); -- new value of the register
                   be  : in std_logic_vector( 7 downto 0)) -- byte enables
     return std_logic_vector is
  variable result : std_logic_vector(val'high downto 0) := reg;
  begin
     for i in 0 to be'high  loop
        if be(i) = '1' then
           result((8*i+7) downto i*8) := val((8*i+7) downto i*8);
        end if;
     end loop;
     return result;
  end write64;

begin

drd_xfer <= RD_REQ and DRD_RDY;
PLLM <= reg_pllm;
PLLN <= reg_plln;

WR_PIPE: process(ICS_CLK)
begin
   if ICS_CLK = '1' and ICS_CLK'event then
      reg_dwr     <= DWR;
      reg_dwr_be  <= DWR_BE;
      reg_wen     <= WEN;
      reg_wr_addr <= WR_ADDR;
   end if;
end process;

CTRL_REGS : process(ICS_CLK,RESET)
begin
   if RESET = '1' then
      DRD_VLD    <= '0';
      rcfg_delay <= X"20";
      sw_reset_i <= '0';
      reg_pllm   <= "001010"; -- M multiply = 10
      reg_plln   <= "00";     -- D divide = 1
   elsif ICS_CLK = '1' and ICS_CLK'event then
      rcfg_start     <= '0';
      force_reconfig <= '0';
      reg_mb_wen     <= '0';
      DRD_VLD        <= RD_REQ;
      PLLOAD0_N      <= '1';
      PLLOAD1_N      <= '1';
      IF1BOOT_WEN    <= '0';
      IF2BOOT_WEN    <= '0';
      -- Write to my registers
      if (reg_wen = '1') and (reg_wr_addr(9 downto 8) = "00") then
         case reg_wr_addr(5 downto 3) is
            when "000" => -- Addr 0x000000 
            when "001" => -- Addr 0x000008
            when "010" => -- Address 0x000010: SYSCTRL register
               if reg_dwr_be(0) = '1' then
                  sw_reset_i <= reg_dwr(0);
               end if;
               if reg_dwr_be(2) = '1' then
                  rev_sel <= reg_dwr(20 downto 16);
               end if;
               if reg_dwr_be(3) = '1' then
                  force_reconfig <= reg_dwr(30);
                  rcfg_start     <= reg_dwr(31);
               end if;
               rcfg_delay <= write64(rcfg_delay&X"00000000000000", reg_dwr, reg_dwr_be)(63 downto 56);
             when "011" => -- 0x000018,0x1C
               if reg_dwr_be(4) = '1' then
                  reg_pllm  <= reg_dwr(32+5 downto 32);
                  reg_plln  <= reg_dwr(32+9 downto 32+8);
                  PLLOAD0_N <= reg_dwr(32+15);
                  PLLOAD1_N <= not reg_dwr(32+15);
               end if;
            when others => null;
         end case;
      end if;
      
      if (reg_wen = '1') and (reg_wr_addr(9 downto 8) = "01") then -- 0x100
         case reg_wr_addr(5 downto 3) is
            when "000" => -- Data/command register
               reg_mb_wen <= '1';
               if reg_dwr_be(4) = '1' then
                  reg_mb_dwr <= write64(reg_mb_dwr&X"00000000", reg_dwr, reg_dwr_be)(63 downto 32);
                  reg_mb_cmd <= '0';
               else
                  reg_mb_dwr <= write64(X"00000000"&reg_mb_dwr, reg_dwr, reg_dwr_be)(31 downto 0);
                  reg_mb_cmd <= '1';
               end if;
            when "001" => -- Addr 0x000108
            when "010" => -- Addr 0x000110
            when "011" => -- Addr 0x000118
            when others => null;
         end case;
      end if;
      
      if (reg_wen = '1') and (reg_wr_addr(9 downto 8) = "10") then -- 0x200
         case reg_wr_addr(5 downto 3) is
            when "000" => -- Addr 0x000200 
               if reg_dwr_be(0) = '1' then
                  IF1BOOT_PROG <= reg_dwr(0);
               elsif reg_dwr_be(4) = '1' then
                  IF1BOOT_DATA <= reg_dwr(63 downto 32);
                  IF1BOOT_WEN  <= '1';
               end if;
            when "001" => -- Addr 0x000208
               if reg_dwr_be(0) = '1' then
                  IF2BOOT_PROG <= reg_dwr(0);
               elsif reg_dwr_be(4) = '1' then
                  IF2BOOT_DATA <= reg_dwr(63 downto 32);
                  IF2BOOT_WEN  <= '1';
               end if;
            when "010" => -- Addr 0x000210
            when "011" => -- Addr 0x000218
            when others => null;
         end case;
      end if;
      
      -- Read from my registers 
      case RD_ADDR(9) & RD_ADDR(8) & RD_ADDR(5 downto 3) is
         when "00000" => DRD <= BUILD_TIME & REVISION; -- 0x000000
         when "00001" => --RESERVED          -- 0x0008
         when "00010" => DRD <= sysctrl_reg; -- 0x0010
         when "00011" => DRD(15 downto  0) <= IF2STAT & IF1STAT; -- 0x0018
                         DRD(23 downto 16) <= SWITCH;
         when "00100" => DRD <= i2c_at_drd;  -- 0x0020
         when "00101" => --RESERVED          -- 0x0024
         when "00110" => DRD <= i2c_if1_drd; -- 0x0030
         when "00111" => DRD <= i2c_if2_drd; -- 0x0038
         when "01000" => DRD <= reg_mb_dwr & X"0000000" & "00" & MB_BUSY & MB_DRDY; -- 0x000100
         when "01001" => -- 0x000108
            DRD     <= MB_DRD & MB_DRD;
            DRD_VLD <= RD_REQ; -- MB_RD_ACK; -- !!!!!!!!!!!!!!!!!!!!!!!!!!
         when "10000" => -- 0x000200
            DRD(1)     <= IF1BOOT_RDY;
         when "10001" => -- 0x000200
            DRD(1)     <= IF2BOOT_RDY;
         when others => null; 
      end case;
   end if;
end process;

-- Async flags
SET_FLAGS: process(reg_wen,reg_wr_addr,RD_REQ,RD_ADDR,DRD_RDY)
begin
   MB_RD_REQ   <= '0';
   i2c_at_wen  <= '0';
   i2c_if1_wen <= '0';   
   i2c_if2_wen <= '0';
   
   if (reg_wen = '1') and (reg_wr_addr(9 downto 8) = "00") then -- Address block 0x0000
      case reg_wr_addr(5 downto 3) is
         when "100"  => i2c_at_wen  <= '1'; -- 0x0020 (I2C controller for the cryptochip)
         when "110"  => i2c_if1_wen <= '1'; -- 0x0030 (I2C controller for IFC1)
         when "111"  => i2c_if2_wen <= '1'; -- 0x0038 (I2C controller for IFC2)
         when others => null;
      end case;
   end if;
   
   if (reg_wen = '1') and (reg_wr_addr(9 downto 8) = "01") then -- Address block 0x0100
      case reg_wr_addr(5 downto 3) is
         when "000" => 
         when "001" => -- Addr 0x000108
         when "010" => -- Addr 0x000110
         when "011" => -- Addr 0x000118
         when others => null;
      end case;
   end if;
   
   -- Read
   if (RD_REQ = '1') and (RD_ADDR(9 downto 8) = "01") then -- Address block 0x0100
      case RD_ADDR(5 downto 3) is
         when "000"  => 
         when "001"  => -- Addr 0x020008 - generate FIFO read request
            MB_RD_REQ <= DRD_RDY; -- !!!!!!!!!!!!!!!!!!!!!!!!!!
         when "010"  => -- Addr 0x020010
         when "011"  => -- Addr 0x020018
         when others => null;
      end case;      
      
   end if; 
end process;

sysctrl_reg <= rcfg_delay & X"000000" & -- 63:32
               delay_cntr_en & "00000000" & recfg_err_reg & delay_cntr_en & rev_sel & -- 31:16
               X"000" & "001" & sw_reset_i; -- 15:0
                            
MB_DWR     <= reg_mb_dwr;
MB_WEN     <= reg_mb_wen;
MB_CMD     <= reg_mb_cmd;

-- MB_FFULL   : in std_logic;
      --
-- MB_DRD     : in  std_logic_vector(31 downto 0);
-- MB_RD      : out std_logic;
-- MB_RD_ACK  : in  std_logic;

-----------------------------------------------------------------------------
-- Device reconfiguration ---------------------------------------------------
-----------------------------------------------------------------------------

RECONF_DELAY : process(RESET, ICS_CLK)
begin
   if RESET = '1' then
      reconfig_i  <= '0';
   elsif ICS_CLK'event and ICS_CLK = '1' then
      -- Delay the start of reconfiguration
      if (reconfig_i = '1') or (RESET = '1') then
         delay_cntr_en <= '0';
      elsif (rcfg_start = '1') then
         delay_cntr_en <= '1';
      end if;
      if (delay_cntr_en = '0') or (RESET = '1') then
         delay_cntr <= rcfg_delay & X"000000";
      elsif (delay_cntr_en = '1') then
         delay_cntr <= delay_cntr - 1;
      end if;
      -- Generate "reconfigure" pulse
      if ((delay_cntr = 0) and (delay_cntr_en = '1')) or (force_reconfig = '1') then
         reconfig_i <= '1';
      elsif icap_en = '0' then
         reconfig_i <= '0';
      end if;
   end if;
end process;

RECONFIG_RECLOCK: process(RESET, CCLK)
begin
   if RESET = '1' then 
      reconfig_gclk  <= '0';
      reconfig_gclk0 <= '0';
   elsif CCLK'event and CCLK = '1' then
      reconfig_gclk0 <= reconfig_i;
      reconfig_gclk  <= reconfig_gclk0;
   end if;
end process;

ICAP_CNTR : process(CCLK)
begin
   if CCLK'event and CCLK = '1' then
      if ((reconfig_gclk = '0') and (icap_en = '1')) or (pulse_cntr = X"F") or (RESET = '1') then
         pulse_cntr <= X"0";
         icap_en    <= '1';
      else
         pulse_cntr <= pulse_cntr + 1;
         icap_en    <= '0';
      end if;
   end if;
end process;

RECONF_ERR_REG : process(CCLK)
begin
   if CCLK'event and CCLK = '1' then
      if (reconfig_gclk = '1') then
         recfg_err_reg <= '0';
      elsif (RECFG_ERR = '1') then
         recfg_err_reg <= '1';
      end if;
   end if;
end process;

-----------------------------------------------------------------------------
-- I2C controllers        ---------------------------------------------------
-----------------------------------------------------------------------------

I2C_AT: entity work.i2c_master_top 
   generic map (PRER_INIT => X"00F9") -- 100KHz
   port map (
      CLK       => ICS_CLK,
      RST_SYNC  => sw_reset_i,
      RST_ASYNC => RESET,
      -- generic bus
      BE        => reg_dwr_be,
      DWR       => reg_dwr,
      DRD       => i2c_at_drd,
      WEN       => i2c_at_wen,
      INT       => open,
      -- i2c lines
      SCL_PAD_I    => CSCL,
      SCL_PAD_O    => i2c_at_scl,
      SCL_PADOEN_O => i2c_at_scl_oen,
      SDA_PAD_I    => CSDA,
      SDA_PAD_O    => i2c_at_sda,
      SDA_PADOEN_O => i2c_at_sda_oen
   );
   
CSDA <= i2c_at_sda when i2c_at_sda_oen = '0' else 'Z';
CSCL <= i2c_at_scl when i2c_at_scl_oen = '0' else 'Z';

I2C_IFC1: entity work.i2c_master_top 
   generic map (PRER_INIT => X"00F9") -- 100KHz
   port map (
      CLK       => ICS_CLK,
      RST_SYNC  => sw_reset_i,
      RST_ASYNC => RESET,
      -- generic bus
      BE        => reg_dwr_be,
      DWR       => reg_dwr,
      DRD       => i2c_if1_drd,
      WEN       => i2c_if1_wen,
      INT       => open,
      -- i2c lines
      SCL_PAD_I    => IF1SCLK,
      SCL_PAD_O    => i2c_if1_scl,
      SCL_PADOEN_O => i2c_if1_scl_oen,
      SDA_PAD_I    => IF1SDA,
      SDA_PAD_O    => i2c_if1_sda,
      SDA_PADOEN_O => i2c_if1_sda_oen
   );
   
IF1SDA  <= i2c_if1_sda when i2c_if1_sda_oen = '0' else 'Z';
IF1SCLK <= i2c_if1_scl when i2c_if1_scl_oen = '0' else 'Z';

I2C_IFC2: entity work.i2c_master_top 
   generic map (PRER_INIT => X"00F9") -- 100KHz
   port map (
      CLK       => ICS_CLK,
      RST_SYNC  => sw_reset_i,
      RST_ASYNC => RESET,
      -- generic bus
      BE        => reg_dwr_be,
      DWR       => reg_dwr,
      DRD       => i2c_if2_drd,
      WEN       => i2c_if2_wen,
      INT       => open,
      -- i2c lines
      SCL_PAD_I    => IF2SCLK,
      SCL_PAD_O    => i2c_if2_scl,
      SCL_PADOEN_O => i2c_if2_scl_oen,
      SDA_PAD_I    => IF2SDA,
      SDA_PAD_O    => i2c_if2_sda,
      SDA_PADOEN_O => i2c_if2_sda_oen
   );
   
IF2SDA  <= i2c_if2_sda when i2c_if2_sda_oen = '0' else 'Z';
IF2SCLK <= i2c_if2_scl when i2c_if2_scl_oen = '0' else 'Z';

-----------------------------------------------------------------------------
-- Output port mapping    ---------------------------------------------------
-----------------------------------------------------------------------------

WR_RDY    <= '1';
RD_ARDY   <= drd_xfer;

RECONFIG  <= reconfig_gclk;       -- Generate the "reconfig" pulse to the CPLD
RECFG_REV <= rev_sel(4 downto 0); -- Revision select, bit
SW_RESET  <= sw_reset_i;

end structural;