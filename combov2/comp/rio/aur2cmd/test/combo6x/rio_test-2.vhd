
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
use work.math_pack.all;

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
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";

      DATA_WIDTH        : integer := 16;
      LANES             : integer := 1;

      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
      );
   port (
      RESET    : in std_logic;
      REFCLK   : in std_logic;
      USRCLK  : in std_logic;
      USRCLK2 : in std_logic;
      
      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0);
      
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


constant MAX_ADDR       : std_logic_vector(8 downto 0) := '1' & X"FF";
--constant MAX_ADDR       : std_logic_vector(8 downto 0) := '0' & x"11"; -- 2 packets
--constant FILL_PATTERN   : std_logic_vector(DATA_WIDTH-33 downto 0) := (others => '1');

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

component aur2cmd is
   generic (
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";

      DATA_WIDTH        : integer;
      LANES             : integer;
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock command protocol interface 
      
      -- Command Protocol TX Interface
      DATA_IN        : in std_logic_vector(DATA_WIDTH-1 downto 0);    -- Data
      CMD_IN         : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);     -- Byte-mapped command flag
      SRC_RDY_IN     : in std_logic;                        -- Source ready flag
      DST_RDY_IN     : out std_logic;                       -- Transmit buffer full flag
 
      -- Command Protocol RX Interface
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);    -- Data
      CMD_OUT        : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);     -- Byte-mapped command flag
      SRC_RDY_OUT    : out std_logic;                        -- DATA_OUT valid flag
      DST_RDY_OUT    : in std_logic;                         -- Destination ready flag
 
      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.

      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0)
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

signal data_to_rio_c      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal cmd_to_rio_c      : std_logic_vector((DATA_WIDTH/8)-1 downto 0);

signal data_to_rio      : std_logic_vector(31 downto 0);
signal cmd_to_rio     : std_logic_vector(3 downto 0);

-- Data from RIO
signal data_from_rio    : std_logic_vector(31 downto 0);
signal cmd_from_rio     : std_logic_vector(3 downto 0);
signal dv_from_rio      : std_logic;
signal dv_from_rio_i    : std_logic;
signal data_from_rio_c  : std_logic_vector(DATA_WIDTH-1 downto 0);
signal cmd_from_rio_c   : std_logic_vector((DATA_WIDTH/8)-1 downto 0);

signal ufc_tx_msg_c     : std_logic_vector(DATA_WIDTH-1 downto 0);

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
   signal reg_dst_rdy_out : std_logic_vector(2 downto 0);

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

rio2cmd_u: aur2cmd
   generic map(
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     => TX_FIFO_ITEMS,
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     => RX_FIFO_ITEMS,
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT,

      DATA_WIDTH        => DATA_WIDTH,
      LANES             => LANES,
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
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
      DATA_IN        => data_to_rio_c,
      CMD_IN         => cmd_to_rio_c,
      SRC_RDY_IN     => reg_tx_active,
      DST_RDY_IN     => open,

      -- Command Protocol RX Interface
      DATA_OUT       => data_from_rio_c,
      CMD_OUT        => cmd_from_rio_c,
      SRC_RDY_OUT    => dv_from_rio_i,
      DST_RDY_OUT    => reg_dst_rdy_out(2),

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

   dv_from_rio <= dv_from_rio_i and reg_dst_rdy_out(2);

   data_to_rio_c     <= data_to_rio(DATA_WIDTH-1 downto 0);
   cmd_to_rio_c      <= cmd_to_rio((DATA_WIDTH/8)-1 downto 0);
   data_from_rio(15 downto 0)     <= data_from_rio_c;
   data_from_rio(31 downto 16)    <= x"0000";
   cmd_from_rio(1 downto 0)  <= cmd_from_rio_c;
   cmd_from_rio(3 downto 2)  <= "00";
   ufc_tx_msg_c      <= (others => '0');


process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_dst_rdy_out(0) <= '1';
      reg_dst_rdy_out(1) <= '0';
      reg_dst_rdy_out(2) <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_dst_rdy_out(1) <= reg_dst_rdy_out(0);
      reg_dst_rdy_out(2) <= reg_dst_rdy_out(1);
      reg_dst_rdy_out(0) <= reg_dst_rdy_out(2);
   end if;
end process;


-- -------------------------------------------------------------
-- Control logic

   tx_active_rst <= '1' when (cnt_tx_addr = MAX_ADDR) else
                    '0';

   rx_active_set <= dv_from_rio;

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
      end if;
   end process;

end behavioral;







