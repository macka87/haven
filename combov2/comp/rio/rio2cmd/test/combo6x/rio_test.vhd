
-- rio_test: RocketIO to Command Protocol Test 
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
use work.commands.ALL; 
use work.rio_codes.ALL;

-- -------------------------------------------------------------
-- Software Address Space
-- -------------------------------------------------------------
--
-- tx_data:       x"0000" - x"0ffc"
-- rx_data:       x"1000" - x"1ffc"
-- reg_tx_active: x"4000"
-- reg_status:    x"4008"

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity rio_test is
   generic (
      BASE       : integer := 0;
      ADDR_WIDTH : integer := 14;
      LOOPBACK : std_logic_vector := "00"
      );
   port (
      RESET    : in std_logic;
      REFCLK   : in std_logic;
      USRCLK  : in std_logic;
      USRCLK2 : in std_logic;
      
      -- MGT Interface
      RXN            : in  std_logic;
      RXP            : in  std_logic;
      TXN            : out std_logic;
      TXP            : out std_logic;
      
      -- Local Bus Interface
      LBCLK     : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME   : in    std_logic;  -- Frame
      LBHOLDA   : out   std_logic;  -- Hold Ack
      LBAD      : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS      : in    std_logic;  -- Adress strobe
      LBRW      : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY     : out   std_logic;  -- Ready
      LBLAST    : in    std_logic   -- Last word in transfer
   );
end entity;
 
-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of rio_test is


   component LBCONN_MEM is
      generic (
         BASE        : integer; -- Base address (28 bit)
         ADDR_WIDTH  : integer  -- Width of address,
      );
      port (
         DATA_OUT : out std_logic_vector(15 downto 0); -- Data output
         DATA_IN  : in  std_logic_vector(15 downto 0); -- Data input
         ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- Address output
         RW       : out std_logic; -- Write/Read#
         EN       : out std_logic; -- Data Enable
         SEL      : out std_logic; -- Select
         DRDY     : in  std_logic; -- Data ready input
         ARDY     : in  std_logic; -- Address Ready (ACK)
         -- local bus interconnection
         RESET    : in  std_logic;
         LBCLK    : in  std_logic;
         LBFRAME  : in  std_logic;
         LBAS     : in  std_logic;
         LBRW     : in  std_logic;
         LBLAST   : in  std_logic;
         LBAD     : inout std_logic_vector(15 downto 0);
         LBHOLDA  : out std_logic;
         LBRDY    : out std_logic
      );
   end component LBCONN_MEM;

component RAMB16_S36_S36 
-- pragma translate_off
  generic (
-- "Read during Write" attribute for functional simulation
	WRITE_MODE_A : string := "READ_FIRST" ; -- WRITE_FIRST(default)/ READ_FIRST/ NO_CHANGE
	WRITE_MODE_B : string := "WRITE_FIRST"  -- WRITE_FIRST(default)/ READ_FIRST/ NO_CHANGE
-- RAM initialization ("0" by default) for functional simulation: see example
	);
-- pragma translate_on
  port (
	DIA     : in std_logic_vector (31 downto 0);
	DIPA    : in std_logic_vector (3 downto 0);
	ADDRA   : in std_logic_vector (8 downto 0);
	ENA     : in std_logic;
	WEA     : in std_logic;
	SSRA    : in std_logic;
	CLKA    : in std_logic;
	DOA     : out std_logic_vector (31 downto 0);
	DOPA    : out std_logic_vector (3 downto 0);	
--
	DIB     : in std_logic_vector (31 downto 0);
	DIPB    : in std_logic_vector (3 downto 0);
	ADDRB   : in std_logic_vector (8 downto 0);
	ENB     : in std_logic;
	WEB     : in std_logic;
	SSRB    : in std_logic;
	CLKB    : in std_logic;
	DOB     : out std_logic_vector (31 downto 0);
	DOPB    : out std_logic_vector (3 downto 0)	
	); 
end component;

component rio2cmd is
   generic (
      LOOPBACK   : std_logic_vector := "00"; -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      TX_LOGIC   : boolean := true;    -- Enables TX logic instantion (in simplex mode for receivers set 'false')
      RX_LOGIC   : boolean := true    -- Enables RX logic instantion (in simplex mode for transmitters set 'false')
      );
   port (
      -- Common Interface
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock command protocol interface

      -- Command Protocol TX Interface
      DI             : in std_logic_vector(31 downto 0);    -- Data
      DI_CMD         : in std_logic_vector(3 downto 0);     -- Byte-mapped command flag
      DI_DV          : in std_logic;                        -- DI valid flag
      DI_FULL        : out std_logic;                       -- Transmit buffer full flag

      -- Command Protocol RX Interface
      DO             : out std_logic_vector(31 downto 0);   -- Data
      DO_CMD         : out std_logic_vector(3 downto 0);    -- Byte-mapped command flag
      DO_DV          : out std_logic;                       -- DO valid flag
      DO_FULL        : in std_logic;                        -- Stop Receiving

      -- Status inteface
      STATUS   : out std_logic_vector(7 downto 0);          -- 0: signals crc error, 1: signals recv buffer overflow
      STATUS_DV: out std_logic;                             -- STATUS is valid

      -- MGT Interface
      RXN            : in  std_logic;
      RXP            : in  std_logic;
      TXN            : out std_logic;
      TXP            : out std_logic
   );
end component;

-- common signals
signal pwr     : std_logic;
signal gnd     : std_logic;

-- registers
signal reg_adc_di    : std_logic_vector(31 downto 0);
signal reg_adc_di_we : std_logic;
signal reg_adc_cmd : std_logic_vector(3 downto 0);
signal reg_adc_cmd_we : std_logic;
signal reg_adc_tx    : std_logic_vector(31 downto 0);
signal adc_tx_we     : std_logic;
signal adc_rx_we     : std_logic;
signal reg_tx_active : std_logic;
signal tx_active_rst : std_logic;
signal reg_tx_active_we : std_logic;
signal reg_rx_active : std_logic;
signal rx_active_set : std_logic;
signal rx_active_rst : std_logic;

signal reg_lb_addr      : std_logic_vector(ADDR_WIDTH-1 downto 0);
signal reg_lb_drdy      : std_logic;

signal reg_status    : std_logic_vector(15 downto 0);

-- counters
signal cnt_tx_addr   : std_logic_vector(8 downto 0);
signal cnt_tx_addr_ce   : std_logic;
signal cnt_rx_addr   : std_logic_vector(8 downto 0);

-- BRAM signals
signal txdata_to_lb  : std_logic_vector(31 downto 0);
signal txcmd_to_lb : std_logic_vector(3 downto 0);
signal rxdata_to_lb  : std_logic_vector(31 downto 0);
signal rxcmd_to_lb : std_logic_vector(3 downto 0);

signal data_to_rio      : std_logic_vector(31 downto 0);
signal cmd_to_rio     : std_logic_vector(3 downto 0);
signal data_to_rio_full : std_logic;

-- Data from RIO
signal data_from_rio    : std_logic_vector(31 downto 0);
signal cmd_from_rio     : std_logic_vector(3 downto 0);
signal dv_from_rio      : std_logic;

-- status signals
signal status           : std_logic_vector(7 downto 0);
signal status_dv        : std_logic;

-- local bus signals
signal lb_data_out      : std_logic_vector(15 downto 0);
signal lb_data_out_i    : std_logic_vector(15 downto 0);
signal lb_data_in       : std_logic_vector(15 downto 0);
signal lb_addr          : std_logic_vector(ADDR_WIDTH-1 downto 0);
signal lb_en            : std_logic;
signal lb_rw            : std_logic;

constant MAX_ADDR       : std_logic_vector(8 downto 0) := '0' & X"11";

begin
pwr <= '1';
gnd <= '0';

-- Block SelectRAM for TX data
U_RAMB_TX: RAMB16_S36_S36
  port map (
	DIA     => reg_adc_di,
	DIPA    => reg_adc_cmd,
	ADDRA   => lb_addr(10 downto 2),
	ENA     => pwr,
	WEA     => adc_tx_we,
	SSRA    => gnd,
	CLKA    => lbclk,
	DOA     => txdata_to_lb,
	DOPA    => txcmd_to_lb,

	DIB     => X"00000000",
	DIPB    => X"0",
	ADDRB   => cnt_tx_addr,
	ENB     => pwr,
	WEB     => gnd,
	SSRB    => gnd,
	CLKB    => lbclk,
	DOB     => data_to_rio,
	DOPB    => cmd_to_rio
	);

-- Block SelectRAM for error records (recieved error pattern)
U_RAMB_RX: RAMB16_S36_S36
  port map (
	DIA     => X"00000000",
	DIPA    => X"0",
	ADDRA   => lb_addr(10 downto 2),
	ENA     => pwr,
	WEA     => gnd,
	SSRA    => gnd,
	CLKA    => lbclk,
	DOA     => rxdata_to_lb,
	DOPA    => rxcmd_to_lb,

	DIB     => data_from_rio,
	DIPB    => cmd_from_rio,
	ADDRB   => cnt_rx_addr,
	ENB     => pwr,
	WEB     => dv_from_rio,
	SSRB    => gnd,
	CLKB    => lbclk,
	DOB     => open,
	DOPB    => open
	);

rio2cmd_u: rio2cmd
   generic map(
      LOOPBACK   => LOOPBACK
      )
   port map (
      -- Common Interface
      RESET          => RESET,
      REFCLK         => REFCLK,
      USRCLK         => USRCLK,
      USRCLK2        => USRCLK2,
      CMDCLK         => LBCLK,

      -- Command Protocol TX Interface
      DI             => data_to_rio,
      DI_CMD         => cmd_to_rio,
      DI_DV          => reg_tx_active,
      DI_FULL        => data_to_rio_full,

      -- Command Protocol RX Interface
      DO             => data_from_rio,
      DO_CMD         => cmd_from_rio,
      DO_DV          => dv_from_rio,
      DO_FULL        => '0',

      -- Status inteface
      STATUS   => status,
      STATUS_DV=> status_dv,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

-- -------------------------------------------------------------
-- Control logic

   tx_active_rst <= '1' when (cnt_tx_addr = MAX_ADDR) else
                    '0';

   rx_active_set <= '1' when ((data_from_rio(31 downto 24) = C_CMD_SOP) and (cmd_from_rio(3) = '1')
                           and (dv_from_rio = '1')) else
                    '0';

   rx_active_rst <= '1' when cnt_rx_addr = MAX_ADDR else
                    '0';

-- -------------------------------------------------------------
-- Address counters

   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         cnt_tx_addr <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if (tx_active_rst = '1') then
            cnt_tx_addr <= (others => '0');
         elsif (cnt_tx_addr_ce = '1') then
            cnt_tx_addr <= cnt_tx_addr + 1;
         end if;
      end if;
   end process;

   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         cnt_rx_addr <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if (rx_active_rst = '1') then
            cnt_rx_addr <= (others => '0');
         elsif (dv_from_rio = '1') then
            cnt_rx_addr <= cnt_rx_addr + 1;
         end if;
      end if;
   end process;

-- -------------------------------------------------------------
-- Control registers

   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_tx_active <= '0';
      elsif (lbclk'event and lbclk = '1') then
         if (tx_active_rst = '1') then
            reg_tx_active <= '0';
         elsif (reg_tx_active_we = '1') then
            reg_tx_active <= lb_data_out_i(0);
         end if;
      end if;
   end process;

   cnt_tx_addr_ce <= reg_tx_active or reg_tx_active_we;

   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_rx_active <= '0';
      elsif (lbclk'event and lbclk = '1') then
         if (rx_active_rst = '1') then
            reg_rx_active <= '0';
         elsif (rx_active_set = '1') then
            reg_rx_active <= '1';
         end if;
      end if;
   end process;


-- -------------------------------------------------------------
-- LB registers

   -- ModelSIM doesn't clock reg_adc_di register input properly - we need hack:
   lb_data_out_i <=
   --pragma translate_off
   transport
   --pragma translate_on
   lb_data_out
   --pragma translate_off
   after 0.1 ns
   --pragma translate_on
   ;

   -- Data from Local Bus
   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_adc_di <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if (reg_adc_di_we = '1') then
            reg_adc_di(15 downto 0) <= reg_adc_di(31 downto 16);
            reg_adc_di(31 downto 16) <= lb_data_out_i;
         end if;
      end if;
   end process;

   -- Command from Local Bus
   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_adc_cmd <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if (reg_adc_cmd_we = '1') then
            reg_adc_cmd <= lb_data_out_i(3 downto 0);
         end if;
      end if;
   end process;

   -- Registers for LB driving
   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_lb_addr <= (others => '0');
         reg_lb_drdy <= '0';
      elsif (lbclk'event and lbclk = '1') then
         reg_lb_addr <= lb_addr;
         reg_lb_drdy <= (not lb_rw) and lb_en;
      end if;
   end process;

-- -------------------------------------------------------------
-- Address Decoder

   -- Write
   process (lb_addr,lb_en,lb_rw)
   begin
      reg_adc_di_we <= '0';
      reg_adc_cmd_we <= '0';
      adc_tx_we <= '0';
      adc_rx_we <= '0';
      reg_tx_active_we <= '0';
      
      if (lb_addr(13) = '0') then
         if (lb_addr(12 downto 11) = "00") then -- TX BRAM
            if (lb_addr(1) = '1') then -- cmd
               if (lb_addr(0) = '0') then
                  reg_adc_cmd_we <= lb_rw and lb_en;
               else
                  adc_tx_we <= lb_rw and lb_en;
               end if;
            else                       -- data
               reg_adc_di_we <= lb_rw and lb_en;
            end if;
         elsif (lb_addr(12 downto 11) = "01") then -- RX BRAM
            if (lb_addr(1) = '1') then -- cmd
               if (lb_addr(0) = '0') then
                  reg_adc_cmd_we <= lb_rw and lb_en;
               else
                  adc_rx_we <= lb_rw and lb_en;
               end if;
            else                       -- data
               reg_adc_di_we <= lb_rw and lb_en;
            end if;
         end if;
      else     
         -- tx_active register
         if (lb_addr(11 downto 0) = X"000") then
            reg_tx_active_we <=  lb_en and lb_rw;
         end if;
      end if;
   end process;

   -- Read
   process (reg_lb_addr,txdata_to_lb,txcmd_to_lb,rxdata_to_lb,rxcmd_to_lb,reg_tx_active,reg_status)
   begin
      lb_data_in <= (others => '0');
      
      if (reg_lb_addr(13) = '0') then
         if (reg_lb_addr(12 downto 11) = "00") then -- TX BRAM
            if (reg_lb_addr(1) = '0') then
               if (reg_lb_addr(0) = '0') then
                  lb_data_in <= txdata_to_lb(15 downto 0);
               else
                  lb_data_in <= txdata_to_lb(31 downto 16);
               end if;
            else
               if (reg_lb_addr(0) = '0') then
                  lb_data_in(3 downto 0) <= txcmd_to_lb;
               end if;
            end if;
         elsif (reg_lb_addr(12 downto 11) = "01") then -- RX BRAM
            if (reg_lb_addr(1) = '0') then
               if (reg_lb_addr(0) = '0') then
                  lb_data_in <= rxdata_to_lb(15 downto 0);
               else
                  lb_data_in <= rxdata_to_lb(31 downto 16);
               end if;
            else
               if (reg_lb_addr(0) = '0') then
                  lb_data_in(3 downto 0) <= rxcmd_to_lb;
               end if;
            end if;
         end if;
      else
         -- tx_active register
         if (reg_lb_addr(11 downto 0) = X"000") then
            lb_data_in(0) <= reg_tx_active;
         -- reg_status
         elsif (reg_lb_addr(11 downto 0) = X"004") then
            lb_data_in <= reg_status;
         end if;
      end if;
   end process;
   
-- -------------------------------------------------------------
-- LB connect component

   LBCONN_MEM_U: LBCONN_MEM
      generic map(
         ADDR_WIDTH => ADDR_WIDTH,  -- address bus width (12b)
         BASE       => BASE         -- base address
      )
      port map(
         data_out => lb_data_out,
         data_in  => lb_data_in,
         addr     => lb_addr,
         en       => lb_en,
         rw       => lb_rw,
         sel      => open,
         drdy     => reg_lb_drdy,
         ardy     => '1',
         --
         reset    => RESET,
         lbclk    => LBCLK,
         lbframe  => LBFRAME,
         lbas     => LBAS,
         lbrw     => LBRW,
         lblast   => LBLAST,
         lbad     => LBAD,
         lbholda  => LBHOLDA,
         lbrdy    => LBRDY
      );

-- Debug state register
   process (lbclk,RESET)
   begin
      if (RESET = '1') then
         reg_status <= (others => '0');
      elsif (lbclk'event and lbclk = '1') then
         if (reg_tx_active = '1') then
            reg_status(0) <= '1';
         end if;
         if (reg_rx_active = '1') then
            reg_status(1) <= '1';
         end if;
         if (status_dv = '1') then
            reg_status(15 downto 8) <= status;
         end if;
      end if;
   end process;

end behavioral;


