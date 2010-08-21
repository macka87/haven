
-- rio_test: AURVC Component Test 
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
use work.aurvc_pkg.all; 
use work.bp_func.all;

-- -------------------------------------------------------------
-- Software Address Space
-- -------------------------------------------------------------
--
-- tx_data:       x"0000" - x"1ffc"
-- reg_tx_active: x"1000"
-- reg_status:    x"1008" 
-- bus_probe0:    x"2000"
--    mem:           x"1000"
-- bus_probei:    bus_probe0 + (i * x"2000")
--    mem:           x"1000"

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity aurvc_test is
   generic (
      BASE       : integer := 0;
      ADDR_WIDTH : integer := 13;

      LANES      : integer;
      DATA_PATHS : integer := 2;

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
architecture behavioral of aurvc_test is


   constant TX_CHANNELS : integer   := 1;
   constant RX_CHANNELS : integer   := 4;
   constant MAX_ADDR       : std_logic_vector(11 downto 0) := X"3C5"; 

   constant BUFFERS_PARAM : t_aurvc_buffers_param := (
      (
         (channel_size => 1023, byte_quota => 64),
         others => (channel_size => 0, byte_quota => 64)
      ),
      (
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110", rx_is_header => true, rx_is_footer => false),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110", rx_is_header => true, rx_is_footer => false),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110", rx_is_header => true, rx_is_footer => false),
         (channel_size => 1023, xon_limit => "011", xoff_limit => "110", rx_is_header => true, rx_is_footer => false),
         others => (channel_size => 0, xon_limit => "011", xoff_limit => "110", rx_is_header => true, rx_is_footer => false)
      )
   );

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

component RAMB16_S18_S18 
-- pragma translate_off
  generic (
-- "Read during Write" attribute for functional simulation
	WRITE_MODE_A : string := "READ_FIRST" ; -- WRITE_FIRST(default)/ READ_FIRST/ NO_CHANGE
	WRITE_MODE_B : string := "WRITE_FIRST"   -- WRITE_FIRST(default)/ READ_FIRST/ NO_CHANGE
-- RAM initialization ("0" by default) for functional simulation: see example
  	);
-- pragma translate_on
  port (
	DIA     : in std_logic_vector (15 downto 0);
	DIPA    : in std_logic_vector (1 downto 0);
	ADDRA   : in std_logic_vector (9 downto 0);        
	ENA     : in std_logic;
	WEA     : in std_logic;
	SSRA    : in std_logic;
	CLKA    : in std_logic;
	DOA     : out std_logic_vector (15 downto 0);
	DOPA    : out std_logic_vector (1 downto 0);	
--
	DIB     : in std_logic_vector (15 downto 0);
	DIPB    : in std_logic_vector (1 downto 0);
	ADDRB   : in std_logic_vector (9 downto 0);        
	ENB     : in std_logic;
	WEB     : in std_logic;
	SSRB    : in std_logic;
	CLKB    : in std_logic;
	DOB     : out std_logic_vector (15 downto 0);
	DOPB    : out std_logic_vector (1 downto 0)	
	); 
end component;

component aurvc is
   generic (
      DATA_PATHS           : integer;                 -- Number of bytes of data port
      LANES                : integer;
      TX_CHANNELS          : integer;                 -- Number of TX channels
      RX_CHANNELS          : integer;                 -- Number of RX channels
      BUFFERS_PARAM        : t_aurvc_buffers_param;   -- Buffers' parameters
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      FLCLK          : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- FrameLink TX Interface
      TX_D             : in std_logic_vector((TX_CHANNELS*(DATA_PATHS*8))-1 downto 0);
      TX_REM           : in std_logic_vector((TX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
      TX_SRC_RDY_N     : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_SOF_N         : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_SOP_N         : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_EOF_N         : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_EOP_N         : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_DST_RDY_N    : out std_logic_vector(TX_CHANNELS-1 downto 0);

      -- FrameLink RX Interface
      RX_D             : out std_logic_vector((RX_CHANNELS*(DATA_PATHS*8))-1 downto 0);
      RX_REM           : out std_logic_vector((RX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
      RX_SRC_RDY_N     : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_SOF_N         : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_SOP_N         : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_EOF_N         : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_EOP_N         : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_DST_RDY_N     : in std_logic_vector(RX_CHANNELS-1 downto 0);

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

component BUSPROBE is
   generic(
       BASE             : integer;
       ADC_FREQUENCY    : integer := 50;
       -- width of monitored bus:
       BUS_WIDTH        : integer;
       -- number of items in buffer:
       BUFFER_SIZE      : integer;
       -- Block Ram Type, only 1, 2, 4, 8, 16, 32 bits
       BRAM_TYPE        : integer
   );
   port(
      CLK               : in std_logic;
      SAMPLE_CLK        : in std_logic;
      RESET             : in std_logic;

      -- hardware interface
      EN                : in std_logic;
      WEN               : in std_logic;
      START_TRIGGER     : in std_logic;
      STOP_TRIGGER      : in std_logic;
      TOGGLE_TRIGGER    : in std_logic;
      MONITORED_BUS     : in std_logic_vector(BUS_WIDTH-1 downto 0);

      -- local bus interface
      LBCLK             : in    std_logic;
      LBFRAME           : in    std_logic;
      LBHOLDA           : out   std_logic;
      LBAD              : inout std_logic_vector(15 downto 0);
      LBAS              : in    std_logic;
      LBRW              : in    std_logic;
      LBRDY             : out   std_logic;
      LBLAST            : in    std_logic
   );
end component;

   constant BUFFER_SIZE  : integer := 1024;
   constant BUS_WIDTH    : integer := log2(DATA_PATHS) + 4 + (DATA_PATHS*8);
   constant BRAM_TYPE    : integer := 32;

   constant BP_BASE_ADDR    : integer := (BASE + (2**(ADDR_WIDTH+1))); -- first bus probe base addr
   constant BP_NEXT         : integer := 2**BP_ADDR_WIDTH(BUFFER_SIZE, BUS_WIDTH, BRAM_TYPE); -- offset to next Bus Probe

-- common signals
signal pwr     : std_logic;
signal gnd     : std_logic;

-- registers
signal reg_adc_di    : std_logic_vector(15 downto 0);
signal reg_adc_di_we : std_logic;
signal adc_ctrl : std_logic_vector(1 downto 0);
signal reg_adc_tx    : std_logic_vector(15 downto 0);
signal adc_tx_we     : std_logic;
signal reg_tx_active : std_logic;
signal tx_active_rst : std_logic;
signal reg_tx_active_we : std_logic;
signal reg_sop       : std_logic;

signal reg_lb_addr      : std_logic_vector(ADDR_WIDTH-1 downto 0);
signal reg_lb_drdy      : std_logic;

signal reg_status    : std_logic_vector(15 downto 0);

-- counters
signal cnt_tx_addr   : std_logic_vector(9 downto 0);
signal cnt_tx_addr_ce   : std_logic;

-- BRAM signals
signal txdata_to_lb  : std_logic_vector(15 downto 0);
signal txctrl_to_lb : std_logic_vector(1 downto 0);

signal data_to_aurvc      : std_logic_vector(15 downto 0);
signal ctrl_to_aurvc     : std_logic_vector(1 downto 0);

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

   -- aurvc signals
   signal tx_d             : std_logic_vector((TX_CHANNELS*(DATA_PATHS*8))-1 downto 0); 
   signal tx_rem           : std_logic_vector((TX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
   signal tx_src_rdy_n     : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_sof_n         : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_sop_n         : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_eof_n         : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_eop_n         : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_dst_rdy_n     : std_logic_vector(TX_CHANNELS-1 downto 0); 
   signal tx_dst_rdy_n_i   : std_logic_vector(TX_CHANNELS downto 0); 
   signal aurvc_rdy        : std_logic;   -- all aurvc dst_rdy are set

   signal rx_d          : std_logic_vector((RX_CHANNELS*(DATA_PATHS*8))-1 downto 0); 
   signal rx_rem        : std_logic_vector((RX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
   signal rx_src_rdy_n  : std_logic_vector(RX_CHANNELS-1 downto 0); 
   signal rx_sof_n      : std_logic_vector(RX_CHANNELS-1 downto 0); 
   signal rx_sop_n      : std_logic_vector(RX_CHANNELS-1 downto 0); 
   signal rx_eof_n      : std_logic_vector(RX_CHANNELS-1 downto 0); 
   signal rx_eop_n      : std_logic_vector(RX_CHANNELS-1 downto 0); 
   signal rx_dst_rdy_n  : std_logic_vector(RX_CHANNELS-1 downto 0); 

   -- Bus Probe signals
   signal monitored_bus    : std_logic_vector((RX_CHANNELS*(BUS_WIDTH))-1 downto 0);
   signal bp_wen           : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal start_trigger    : std_logic_vector(RX_CHANNELS-1 downto 0);
   signal stop_trigger     : std_logic_vector(RX_CHANNELS-1 downto 0);
 
begin
pwr <= '1';
gnd <= '0';

-- Block SelectRAM for TX data
U_RAMB_TX: RAMB16_S18_S18
  port map (
	DIA     => reg_adc_di,
	DIPA    => adc_ctrl,
	ADDRA   => lb_addr(10 downto 1),
	ENA     => pwr,
	WEA     => adc_tx_we,
	SSRA    => gnd,
	CLKA    => LBCLK,
	DOA     => txdata_to_lb,
	DOPA    => txctrl_to_lb,

	DIB     => X"0000",
	DIPB    => "00",
	ADDRB   => cnt_tx_addr,
	ENB     => pwr,
	WEB     => gnd,
	SSRB    => gnd,
	CLKB    => LBCLK,
	DOB     => data_to_aurvc,
	DOPB    => ctrl_to_aurvc
	);

aurvc_u: aurvc
   generic map (
      LANES                => LANES,
      DATA_PATHS           => DATA_PATHS,
      TX_CHANNELS          => TX_CHANNELS,
      RX_CHANNELS          => RX_CHANNELS,
      BUFFERS_PARAM        => BUFFERS_PARAM,
      LOOPBACK             => LOOPBACK 
   )
   port map (
      -- Common Input
      RESET          => RESET,
      REFCLK         => REFCLK,
      USRCLK         => USRCLK,
      USRCLK2        => USRCLK2,
      FLCLK          => LBCLK,
      
      -- FrameLink TX Interface
      TX_D             => tx_d,
      TX_REM           => tx_rem,
      TX_SRC_RDY_N     => tx_src_rdy_n,
      TX_SOF_N         => tx_sof_n,
      TX_SOP_N         => tx_sop_n,
      TX_EOF_N         => tx_eof_n,
      TX_EOP_N         => tx_eop_n,
      TX_DST_RDY_N     => tx_dst_rdy_n,

      -- FrameLink RX Interface
      RX_D             => rx_d,
      RX_REM           => rx_rem,
      RX_SRC_RDY_N     => rx_src_rdy_n,
      RX_SOF_N         => rx_sof_n,
      RX_SOP_N         => rx_sop_n,
      RX_EOF_N         => rx_eof_n,
      RX_EOP_N         => rx_eop_n,
      RX_DST_RDY_N     => rx_dst_rdy_n,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => open,
      SOFT_ERROR     => open,
      FRAME_ERROR    => open,
                                          -- and is asserted for a single clock.
      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

-- -------------------------------------------------------------
-- TX part
-- -------------------------------------------------------------

-- -------------------------------------------------------------
-- TX data mapping to AURVC

tx_dst_rdy_n_i(0) <= '0';

tx_data_gen: for i in 0 to TX_CHANNELS-1 generate
   tx_d(((i+1)*DATA_PATHS*8)-1 downto (i*DATA_PATHS*8)) <= data_to_aurvc xor conv_std_logic_vector(i,DATA_PATHS*8);
   tx_rem(i) <= ctrl_to_aurvc(0);
   tx_src_rdy_n(i) <= not (reg_tx_active and aurvc_rdy);
   tx_sof_n(i) <= not reg_sop;
   tx_sop_n(i) <= not reg_sop;
   tx_eof_n(i) <= not ctrl_to_aurvc(1);
   tx_eop_n(i) <= not ctrl_to_aurvc(1);
   tx_dst_rdy_n_i(i+1) <= tx_dst_rdy_n_i(i) or tx_dst_rdy_n(i);
end generate;

aurvc_rdy <= not tx_dst_rdy_n_i(TX_CHANNELS);
   
-- -------------------------------------------------------------
-- Control logic

   tx_active_rst <= '1' when (cnt_tx_addr = MAX_ADDR(9 downto 0)) else
                    '0';

-- -------------------------------------------------------------
-- Address counters

   process (LBCLK,RESET)
   begin
      if (RESET = '1') then
         cnt_tx_addr <= (others => '0');
      elsif (LBCLK'event and LBCLK = '1') then
         if (tx_active_rst = '1') then
            cnt_tx_addr <= (others => '0');
         elsif (cnt_tx_addr_ce = '1') then
            cnt_tx_addr <= cnt_tx_addr + 1;
         end if;
      end if;
   end process;

-- -------------------------------------------------------------
-- Control registers

   process (LBCLK,RESET)
   begin
      if (RESET = '1') then
         reg_tx_active <= '0';
      elsif (LBCLK'event and LBCLK = '1') then
         if (tx_active_rst = '1') then
            reg_tx_active <= '0';
         elsif (reg_tx_active_we = '1') then
            reg_tx_active <= lb_data_out_i(0);
         end if;
      end if;
   end process;

   cnt_tx_addr_ce <= (reg_tx_active or reg_tx_active_we) and aurvc_rdy;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_sop <= '1';
   elsif (LBCLK'event AND LBCLK = '1') then
      if (reg_tx_active = '1') then
         reg_sop <= ctrl_to_aurvc(1);  -- EOP
      end if;
   end if;
end process;

-- -------------------------------------------------------------
-- RX part
-- -------------------------------------------------------------

rx_dst_rdy_n <= (others => '0');

bus_probe_gen: for i in 0 to RX_CHANNELS-1 generate
   monitored_bus(((i+1)*(BUS_WIDTH))-1 downto i*(BUS_WIDTH)) 
         <= rx_rem((i*log2(DATA_PATHS)+log2(DATA_PATHS)-1) downto (i*log2(DATA_PATHS))) 
         & rx_sof_n(i) & rx_sop_n(i) & rx_eof_n(i) & rx_eop_n(i) & 
         rx_d(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8));
   bp_wen(i) <= not rx_src_rdy_n(i);
   start_trigger(i) <= not rx_sop_n(i);
   stop_trigger(i) <= not rx_eop_n(i);

   -- -------------------------------------------------------------
   -- Bus Probe instantiation
   bus_probe_i: BUSPROBE
      generic map(
          BASE             => BP_BASE_ADDR + (i * BP_NEXT),
          ADC_FREQUENCY    => 100,
          -- width of monitored bus:
          BUS_WIDTH        => BUS_WIDTH, -- rem, sof, sop, eof, eop, data
          -- number of items in buffer:
          BUFFER_SIZE      => BUFFER_SIZE,
          -- Block Ram Type, only 1, 2, 4, 8, 16, 32 bits
          BRAM_TYPE        => BRAM_TYPE
      )
      port map(
         CLK               => LBCLK,
         SAMPLE_CLK        => LBCLK,
         RESET             => RESET,
   
         -- hardware interface
         EN                => '1',
         WEN               => bp_wen(i),
         START_TRIGGER     => start_trigger(i),
         STOP_TRIGGER      => stop_trigger(i),
         TOGGLE_TRIGGER    => '0',
         MONITORED_BUS     => monitored_bus(((i+1)*(BUS_WIDTH))-1 downto i*(BUS_WIDTH)),
   
         -- local bus interface
         LBCLK             => LBCLK,
         LBFRAME           => LBFRAME,
         LBHOLDA           => LBHOLDA,
         LBAD              => LBAD,
         LBAS              => LBAS,
         LBRW              => LBRW,
         LBRDY             => LBRDY,
         LBLAST            => LBLAST
      );
end generate;
-- -------------------------------------------------------------
-- Local Bus part
-- -------------------------------------------------------------

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
   process (LBCLK,RESET)
   begin
      if (RESET = '1') then
         reg_adc_di <= (others => '0');
      elsif (LBCLK'event and LBCLK = '1') then
         if (reg_adc_di_we = '1') then
            reg_adc_di <= lb_data_out_i;
         end if;
      end if;
   end process;

   -- Control from Local Bus
   adc_ctrl <= lb_data_out_i(1 downto 0);

   -- Registers for LB driving
   process (LBCLK,RESET)
   begin
      if (RESET = '1') then
         reg_lb_addr <= (others => '0');
         reg_lb_drdy <= '0';
      elsif (LBCLK'event and LBCLK = '1') then
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
      adc_tx_we <= '0';
      reg_tx_active_we <= '0';
      
      if (lb_addr(11) = '0') then
         if (lb_addr(0) = '1') then -- ctrl
            adc_tx_we <= lb_rw and lb_en;
         else                       -- data
            reg_adc_di_we <= lb_rw and lb_en;
         end if;
      else     
         -- tx_active register
         if (lb_addr(10 downto 0) = X"00"&"000") then
            reg_tx_active_we <=  lb_en and lb_rw;
         end if;
      end if;
   end process;

   -- Read
   process (reg_lb_addr,txdata_to_lb,txctrl_to_lb,reg_tx_active,reg_status)
   begin
      lb_data_in <= (others => '0');
      
      if (reg_lb_addr(11) = '0') then
         if (reg_lb_addr(0) = '0') then
            lb_data_in <= txdata_to_lb;
         else
            lb_data_in(1 downto 0) <= txctrl_to_lb;
         end if;
      else
         -- tx_active register
         if (reg_lb_addr(10 downto 0) = "000" & X"00") then
            lb_data_in(0) <= reg_tx_active;
         -- reg_status
         elsif (reg_lb_addr(10 downto 0) = "000" & X"04") then
            lb_data_in <= reg_status;
         end if;
      end if;
   end process;
   
-- -------------------------------------------------------------
-- LB connect component

   LBCONN_MEM_U: LBCONN_MEM
      generic map(
         ADDR_WIDTH => ADDR_WIDTH,  -- address bus width (12b)
         BASE       => BASE         -- tx_bram base address
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
   process (LBCLK,RESET)
   begin
      if (RESET = '1') then
         reg_status <= (others => '0');
      elsif (LBCLK'event and LBCLK = '1') then
         if (reg_tx_active = '1') then
            reg_status(0) <= '1';
         end if;
      end if;
   end process;

end behavioral;









