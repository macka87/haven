-- rio_gmii.vhd:RocketIO to GMII interface for 10Mb/100Mb/1G Ethernet 
-- Copyright (C) 2005 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
--            Jan Pazdera   <pazdera@liberouter.org>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
--
-- TODO:

library ieee;
use ieee.std_logic_1164.ALL;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- synopsys translate_off
library UNISIM;
use UNISIM.Vcomponents.ALL;
-- synopsys translate_on

entity rio_gmii_debug is
   generic (
       BP_BASE             : integer;
       BASE             : integer;
       BUFFER_SIZE : integer
   );
   port (
      RIO_RCLK  : in  std_logic; -- Precise reference clock for RIO, 62.5MHz
      RIO_DCLK  : in  std_logic; -- 62.5MHz RIO data clk, GMII clk phase aligned
      RESET     : in  std_logic; -- System reset
      -- GMII interface
      GMII_CLK  : in  std_logic; -- 125MHz GMII clock, common for RX and TX
      GMII_RXD  : out std_logic_vector(7 downto 0);
      GMII_RXDV : out std_logic;
      GMII_RXER : out std_logic;
      GMII_TXD  : in  std_logic_vector(7 downto 0);
      GMII_TXEN : in  std_logic;
      GMII_TXER : in  std_logic;
      -- MGT (RocketIO) interface
      RXN       : in  std_logic;
      RXP       : in  std_logic;
      TXN       : out std_logic;
      TXP       : out std_logic;
      -- Status and service interface
      RXPOLARITY: in std_logic;
      TXPOLARITY: in std_logic;
      LOOPBACK  : in std_logic_vector(1 downto 0);
      RXSYNCLOSS: out std_logic;
      -- PHY status interface
      LINK_STATUS       : out std_logic; -- 0: link down, 1: link up
      DUPLEX_MODE       : out std_logic; -- 0: half duplex, 1: full duplex
      SPEED             : out std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             : out std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                         -- 1: SGMII mode active, the PHY status ports are valid
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
end rio_gmii_debug;

architecture behavioral of rio_gmii_debug is

   constant K_SOP : std_logic_vector(7 downto 0) := X"FB";
   constant K_EOP : std_logic_vector(7 downto 0) := X"FD";
   constant K_ERR : std_logic_vector(7 downto 0) := X"FE";
   constant K_CEX : std_logic_vector(7 downto 0) := X"F7";
   constant K28p5 : std_logic_vector(7 downto 0) := X"BC";
   constant K_C1  : std_logic_vector(7 downto 0) := X"B5";
   constant K_C2  : std_logic_vector(7 downto 0) := X"42";

   constant MBUS_WIDTH : integer := 18;

   attribute ALIGN_COMMA_MSB          : string ;
   attribute CHAN_BOND_LIMIT          : string ;
   attribute CHAN_BOND_MODE           : string ;
   attribute CHAN_BOND_OFFSET         : string ;
   attribute CHAN_BOND_ONE_SHOT       : string ;
   attribute CHAN_BOND_SEQ_2_USE      : string ;
   attribute CHAN_BOND_SEQ_LEN        : string ;
   attribute CHAN_BOND_WAIT           : string ;
   attribute CLK_CORRECT_USE          : string ;
   attribute CLK_COR_SEQ_1_1          : string ;
   attribute CLK_COR_SEQ_1_2          : string ;
   attribute CLK_COR_SEQ_2_USE        : string ;
   attribute CLK_COR_SEQ_LEN          : string ;
   attribute COMMA_10B_MASK           : string ;
   attribute CRC_END_OF_PKT           : string ;
   attribute CRC_FORMAT               : string ;
   attribute CRC_START_OF_PKT         : string ;
   attribute DEC_MCOMMA_DETECT        : string ;
   attribute DEC_PCOMMA_DETECT        : string ;
   attribute DEC_VALID_COMMA_ONLY     : string ;
   attribute MCOMMA_10B_VALUE         : string ;
   attribute MCOMMA_DETECT            : string ;
   attribute PCOMMA_10B_VALUE         : string ;
   attribute PCOMMA_DETECT            : string ;
   attribute RX_BUFFER_USE            : string ;
   attribute RX_DATA_WIDTH            : string ;
   attribute RX_DECODE_USE            : string ;
   attribute TX_BUFFER_USE            : string ;
   attribute TX_DATA_WIDTH            : string ;
   attribute CLK_COR_INSERT_IDLE_FLAG : string ;
   attribute CLK_COR_KEEP_IDLE        : string ;
   attribute CLK_COR_REPEAT_WAIT      : string ;
   attribute RX_CRC_USE               : string ;
   attribute RX_LOSS_OF_SYNC_FSM      : string ;
   attribute RX_LOS_INVALID_INCR      : string ;
   attribute RX_LOS_THRESHOLD         : string ;
   attribute TERMINATION_IMP          : string ;
   attribute SERDES_10B               : string ;
   attribute TX_CRC_FORCE_VALUE       : string ;
   attribute TX_CRC_USE               : string ;
   attribute TX_DIFF_CTRL             : string ;
   attribute TX_PREEMPHASIS           : string ;
   attribute REF_CLK_V_SEL            : string ;

   -- RIO Ethernet component -------------------------------------------------
   component GT_ETHERNET_2
   -- synopsys translate_off
   generic (
      CLK_COR_INSERT_IDLE_FLAG : boolean :=  FALSE;
      CLK_COR_KEEP_IDLE : boolean :=  FALSE;
      CLK_COR_REPEAT_WAIT : integer :=  1;
      RX_CRC_USE : boolean :=  FALSE;
      RX_LOSS_OF_SYNC_FSM : boolean :=  TRUE;
      RX_LOS_INVALID_INCR : integer :=  1;
      RX_LOS_THRESHOLD : integer :=  4;
      TERMINATION_IMP : integer :=  50;
      SERDES_10B : boolean :=  FALSE;
      TX_CRC_FORCE_VALUE : bit_vector :=  "11010110";
      TX_CRC_USE : boolean :=  FALSE;
      TX_DIFF_CTRL : integer :=  500;
      TX_PREEMPHASIS : integer :=  0;
      REF_CLK_V_SEL : integer :=  1
    );
    -- synopsys translate_on
    port (
       CONFIGENABLE   : in    std_logic;
       CONFIGIN       : in    std_logic;
       ENMCOMMAALIGN  : in    std_logic;
       ENPCOMMAALIGN  : in    std_logic;
       LOOPBACK       : in    std_logic_vector (1 downto 0);
       POWERDOWN      : in    std_logic;
       REFCLK         : in    std_logic;
       REFCLK2        : in    std_logic;
       REFCLKSEL      : in    std_logic;
       BREFCLK        : in    std_logic;
       BREFCLK2       : in    std_logic;
       RXN            : in    std_logic;
       RXP            : in    std_logic;
       RXPOLARITY     : in    std_logic;
       RXRESET        : in    std_logic;
       RXUSRCLK       : in    std_logic;
       RXUSRCLK2      : in    std_logic;
       TXBYPASS8B10B  : in    std_logic_vector (1 downto 0);
       TXCHARDISPMODE : in    std_logic_vector (1 downto 0);
       TXCHARDISPVAL  : in    std_logic_vector (1 downto 0);
       TXCHARISK      : in    std_logic_vector (1 downto 0);
       TXDATA         : in    std_logic_vector (15 downto 0);
       TXFORCECRCERR  : in    std_logic;
       TXINHIBIT      : in    std_logic;
       TXPOLARITY     : in    std_logic;
       TXRESET        : in    std_logic;
       TXUSRCLK       : in    std_logic;
       TXUSRCLK2      : in    std_logic;
       CONFIGOUT      : out   std_logic;
       RXBUFSTATUS    : out   std_logic_vector (1 downto 0);
       RXCHARISCOMMA  : out   std_logic_vector (1 downto 0);
       RXCHARISK      : out   std_logic_vector (1 downto 0);
       RXCHECKINGCRC  : out   std_logic;
       RXCLKCORCNT    : out   std_logic_vector (2 downto 0);
       RXCOMMADET     : out   std_logic;
       RXCRCERR       : out   std_logic;
       RXDATA         : out   std_logic_vector (15 downto 0);
       RXDISPERR      : out   std_logic_vector (1 downto 0);
       RXLOSSOFSYNC   : out   std_logic_vector (1 downto 0);
       RXNOTINTABLE   : out   std_logic_vector (1 downto 0);
       RXREALIGN      : out   std_logic;
       RXRECCLK       : out   std_logic;
       RXRUNDISP      : out   std_logic_vector (1 downto 0);
       TXBUFERR       : out   std_logic;
       TXKERR         : out   std_logic_vector (1 downto 0);
       TXN            : out   std_logic;
       TXP            : out   std_logic;
       TXRUNDISP      : out   std_logic_vector (1 downto 0)
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
end component BUSPROBE;

   attribute ALIGN_COMMA_MSB of GT_ETHERNET_2      : component is "TRUE";
   attribute CHAN_BOND_LIMIT of GT_ETHERNET_2      : component is "1";
   attribute CHAN_BOND_MODE of GT_ETHERNET_2       : component is "OFF";
   attribute CHAN_BOND_OFFSET of GT_ETHERNET_2     : component is "0";
   attribute CHAN_BOND_ONE_SHOT of GT_ETHERNET_2   : component is "TRUE";
   attribute CHAN_BOND_SEQ_2_USE of GT_ETHERNET_2  : component is "FALSE";
   attribute CHAN_BOND_SEQ_LEN of GT_ETHERNET_2    : component is "1";
   attribute CHAN_BOND_WAIT of GT_ETHERNET_2       : component is "7";
   attribute CLK_CORRECT_USE of GT_ETHERNET_2      : component is "TRUE";
   attribute CLK_COR_SEQ_1_1 of GT_ETHERNET_2      : component is "00110111100";
   attribute CLK_COR_SEQ_1_2 of GT_ETHERNET_2      : component is "00001010000";
   attribute CLK_COR_SEQ_2_USE of GT_ETHERNET_2    : component is "FALSE";
   attribute CLK_COR_SEQ_LEN of GT_ETHERNET_2      : component is "2";
   attribute COMMA_10B_MASK of GT_ETHERNET_2       : component is "1111111000";
   attribute CRC_END_OF_PKT of GT_ETHERNET_2       : component is "K29_7";
   attribute CRC_FORMAT of GT_ETHERNET_2           : component is "ETHERNET";
   attribute CRC_START_OF_PKT of GT_ETHERNET_2     : component is "K27_7";
   attribute DEC_MCOMMA_DETECT of GT_ETHERNET_2    : component is "TRUE";
   attribute DEC_PCOMMA_DETECT of GT_ETHERNET_2    : component is "TRUE";
   attribute DEC_VALID_COMMA_ONLY of GT_ETHERNET_2 : component is "TRUE";
   attribute MCOMMA_10B_VALUE of GT_ETHERNET_2     : component is "1100000000";
   attribute MCOMMA_DETECT of GT_ETHERNET_2        : component is "TRUE";
   attribute PCOMMA_10B_VALUE of GT_ETHERNET_2     : component is "0011111000";
   attribute PCOMMA_DETECT of GT_ETHERNET_2        : component is "TRUE";
   attribute RX_BUFFER_USE of GT_ETHERNET_2        : component is "TRUE";
   attribute RX_DATA_WIDTH of GT_ETHERNET_2        : component is "2";
   attribute RX_DECODE_USE of GT_ETHERNET_2        : component is "TRUE";
   attribute TX_BUFFER_USE of GT_ETHERNET_2        : component is "TRUE";
   attribute TX_DATA_WIDTH of GT_ETHERNET_2        : component is "2";

   attribute CLK_COR_INSERT_IDLE_FLAG of GT_ETHERNET_INST : label is "FALSE";
   attribute CLK_COR_KEEP_IDLE of GT_ETHERNET_INST        : label is "FALSE";
   attribute CLK_COR_REPEAT_WAIT of GT_ETHERNET_INST      : label is "1";
   attribute RX_CRC_USE of GT_ETHERNET_INST               : label is "FALSE";
   attribute RX_LOSS_OF_SYNC_FSM of GT_ETHERNET_INST      : label is "TRUE";
   attribute RX_LOS_INVALID_INCR of GT_ETHERNET_INST      : label is "1";
   attribute RX_LOS_THRESHOLD of GT_ETHERNET_INST         : label is "64";
   attribute TERMINATION_IMP of GT_ETHERNET_INST          : label is "75";
   attribute TX_CRC_FORCE_VALUE of GT_ETHERNET_INST       : label is "11010110";
   attribute TX_CRC_USE of GT_ETHERNET_INST               : label is "FALSE";
   attribute TX_DIFF_CTRL of GT_ETHERNET_INST             : label is "700";
   attribute TX_PREEMPHASIS of GT_ETHERNET_INST           : label is "2";
   attribute REF_CLK_V_SEL of GT_ETHERNET_INST            : label is "1";
   attribute SERDES_10B of GT_ETHERNET_INST               : label is "TRUE";

   signal GND          : std_logic;
   signal PWR          : std_logic;
   signal rst_cntr     : std_logic_vector(4 downto 0);
   signal reset_i      : std_logic;
   signal rxclk        : std_logic;
   signal cycle        : std_logic := '1';
   signal rx_cycle     : std_logic := '0';
   signal txdata_swp   : std_logic_vector(9 downto 0);
   signal txdata       : std_logic_vector(9 downto 0);
   signal reg_txdata   : std_logic_vector(19 downto 0);
   signal rio_txdata   : std_logic_vector(19 downto 0);
   signal rio_txdata_i : std_logic_vector(19 downto 0);
   signal rxdata       : std_logic_vector(15 downto 0);
   signal rxdisperr    : std_logic_vector(1 downto 0);
   signal rxlossofsync : std_logic_vector(1 downto 0);
   signal rxnotintable : std_logic_vector(1 downto 0);
   signal rxcharisk    : std_logic_vector(1 downto 0);
   signal rxchariscomma: std_logic_vector(1 downto 0);
   signal rxdata_dly       : std_logic_vector(15 downto 0);
   signal rxdisperr_dly    : std_logic_vector(1 downto 0);
   signal rxlossofsync_dly : std_logic_vector(1 downto 0);
   signal rxnotintable_dly : std_logic_vector(1 downto 0);
   signal rxcharisk_dly    : std_logic_vector(1 downto 0);
   signal rio_rxdata       : std_logic_vector(15 downto 0);
   signal rio_rxdisperr    : std_logic_vector(1 downto 0);
   signal rio_rxnotintable : std_logic_vector(1 downto 0);
   signal rio_rxcharisk    : std_logic_vector(1 downto 0);
   signal reg_rio_rxdata       : std_logic_vector(15 downto 0);   
   signal reg_rio_rxdisperr    : std_logic_vector(1 downto 0);
   signal reg_rio_rxnotintable : std_logic_vector(1 downto 0);
   signal reg_rio_rxcharisk    : std_logic_vector(1 downto 0);   
   signal reg_rxdisperr    : std_logic;
   signal reg_rxnotintable : std_logic;
   signal reg_rxcharisk    : std_logic;
   signal reg_rxdata       : std_logic_vector(7 downto 0);
   signal rio_sop      : std_logic_vector(1 downto 0);
   signal reg_rio_sop  : std_logic_vector(1 downto 0);
   signal rx_sop_sync  : std_logic;
   signal rx_char_val  : std_logic;
   signal rx_kchar_val : std_logic;
   signal rx_idle      : std_logic;
   signal rx_sop       : std_logic;
   signal rx_eop       : std_logic;
   signal reg_rx_eop   : std_logic;
   signal rx_err       : std_logic; -- 
   signal rx_cex       : std_logic; -- Carrier extend
   signal rx_ferr      : std_logic; -- 
   signal rx_eeop      : std_logic; -- 
   signal rx_fc        : std_logic; -- 
   signal rx_data_mx   : std_logic_vector(7 downto 0);
   signal reg_rxer     : std_logic;
   signal reg_rxd      : std_logic_vector(7 downto 0);
   signal reg_rxdv     : std_logic;
   signal tx_sop       : std_logic;
   signal rx_realign   : std_logic;
   signal gmii_rx_dv   : std_logic;
   signal reg_gmii_txd : std_logic_vector(7 downto 0);
   signal reg_gmii_txdv: std_logic;

   signal lb_en          : std_logic;
   signal lb_rw          : std_logic;
   signal lb_addr        : std_logic_vector(3 downto 0);
   signal lb_di          : std_logic_vector(15 downto 0);
   signal lb_do          : std_logic_vector(15 downto 0);
   signal lb_drdy        : std_logic;
   signal lb_ardy        : std_logic;

   signal monitored_bus : std_logic_vector(MBUS_WIDTH-1 downto 0);
   signal start_trig : std_logic;
   signal stop_trig : std_logic;
   signal not_idle : std_logic;
   signal cnt_bp : std_logic_vector(31 downto 0);
   signal cnt_bp_ce : std_logic;
   signal counter_rst : std_logic;
   signal bp_wen : std_logic;
   signal bp_di  : std_logic_vector(MBUS_WIDTH-1 downto 0);

   signal config_present : std_logic;
   signal reg_config_present : std_logic;
   signal reg_last_config : std_logic_vector(17 downto 0);
   signal reg_last_config_we : std_logic;
   signal reg_last_config_we_pipe : std_logic;

   signal reg_sndack : std_logic;
   signal cnt_sndack : std_logic_vector(1 downto 0);
   signal cnt_sndack_rst : std_logic;
   signal cnt_sndack_ce : std_logic;
   signal sndack_data : std_logic_vector(19 downto 0);
   signal reg_phystatus : std_logic_vector(15 downto 0);
   signal reg_phystatus_we : std_logic;
   signal reg_packet_rcv : std_logic;
   signal reg_packet_rcv_we : std_logic;

begin

GND <= '0';
PWR <= '1';

POWERUP_RESET: process(RIO_DCLK)
begin
   if RIO_DCLK'event and RIO_DCLK = '1' then
      if (RESET = '1') then
         rst_cntr <= (others => '0');
      else
         rst_cntr <= rst_cntr + 1;
      end if;
         
      if (RESET = '1') then
         reset_i <= '1';
      elsif rst_cntr(rst_cntr'high) = '1' then
         reset_i <= '0';
      end if;
   end if;
end process;
   
-- ---------------------------------------------------------------------------
-- -- TX, GMII to SFP conversion --
-- ---------------------------------------------------------------------------

   -- TX data PCS and 8b/10b conversion
   GMII2SFP_PCS : entity work.pcs_mx_out
   port map(
      RESET     => reset_i,         -- combo6 reset
      TX_CLK    => GMII_CLK,      -- 10b output clock
      TX_D      => reg_gmii_txd,  -- GMII 8b data
      TX_EN     => reg_gmii_txdv, -- GMII data valid
      TX_ERR    => GMII_TXER,     -- GMII data error
      
      DATA_8    => txdata_swp(7 downto 0),
      DATA_8_K  => txdata_swp(8),
      DATA_10   => txdata        -- 10b output data
   );
   
   txdata_swp(9) <= '0';
                
   tx_sop <= '1' when (txdata_swp(8) = '1') and (txdata_swp(7 downto 0) = K_SOP) 
             else '0';

   TXDATA_REG : process(reset_i,GMII_CLK)
   begin
      if reset_i = '1' then
         reg_txdata    <= "01" & X"BC" & "00" & X"50"; -- IDLE pattern
         cycle         <= '1'; -- !! Do not change 
         reg_gmii_txdv <= '0';
         reg_gmii_txd  <= (others => '0');
      elsif GMII_CLK'event and GMII_CLK = '1' then
         cycle          <= not cycle;
         reg_gmii_txd   <= GMII_TXD;
         reg_gmii_txdv  <= GMII_TXEN;
         if (cycle = '1') then
            reg_txdata(19 downto 10) <= txdata_swp;
         else
            reg_txdata( 9 downto  0) <= txdata_swp;
         end if;
      end if;
   end process;

-- ---------------------------------------------------------------------------
-- -- RX, SFP to GMII conversion --
-- ---------------------------------------------------------------------------

rx_char_val  <= (not reg_rxnotintable) and (not reg_rxdisperr);
rx_kchar_val <= reg_rxcharisk and rx_char_val;

rx_idle <= '1' when (rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K28p5) 
           else '0';
-- Start of frame
rx_sop  <= '1' when (rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_SOP) 
           else '0';
-- End of frame
rx_eop  <= '1' when (rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_EOP) 
           else '0';
-- Error propagation           
rx_err  <= '1' when (rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_ERR)
           else '0';
-- Carrier extend
rx_cex  <= '1' when (rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_CEX)
                    and (reg_rx_eop = '0')
           else '0';
-- False carrier
rx_fc   <= (not gmii_rx_dv) and (not reg_rx_eop) and
             (rx_kchar_val and (not rx_idle) and (not rx_sop) and (not rx_cex));
-- Error inside the frame
rx_ferr <= gmii_rx_dv and 
              ((rx_kchar_val and (not rx_eop)) or (not rx_char_val));
-- Early end of frame
rx_eeop <= gmii_rx_dv and (rx_idle or rx_cex);

rx_data_mx <= X"55" when rx_sop = '1' else 
              X"0F" when rx_cex = '1' else
              X"0E" when rx_fc = '1'  else
              reg_rxdata;
              
GMII_RX_GEN : process(reset_i,GMII_CLK)
begin
   if reset_i = '1' then
      gmii_rx_dv <= '0';
      reg_rx_eop <= '0';
   elsif GMII_CLK'event and GMII_CLK = '1' then
      if rx_sop = '1' then
         gmii_rx_dv <= '1';
      elsif (rx_eop = '1') or (rx_eeop = '1') then
         gmii_rx_dv <= '0';
      end if;
      reg_rx_eop <= rx_eop;
   end if;
end process;
                
GMII_OUT_REGS: process(reset_i,GMII_CLK)
begin
   if GMII_CLK'event and GMII_CLK = '1' then
      if (reset_i = '1') or (rxlossofsync(1) = '1') then
         reg_rxer <= '0';
         reg_rxd  <= (others => '0');
         reg_rxdv <= '0';
      else
         reg_rxer <= rx_fc or rx_err or rx_ferr or rx_eeop or rx_cex;
         reg_rxd  <= rx_data_mx; 
         reg_rxdv <= (rx_sop or gmii_rx_dv) and (not rx_eop);
      end if;
   end if;
end process;

rio_sop(0) <= '1' when (rxdata(7 downto 0) = K28p5) and 
                         (rxcharisk(0) = '1') and (reg_rio_sop(0) = '0')
              else '0';
rio_sop(1) <= '1' when (rxdata(15 downto 8) = K28p5) and 
                        (rxcharisk(1) = '1') and (reg_rio_sop(1) = '0')
              else '0';
rx_sop_sync <= rio_sop(0) or rio_sop(1);


RIO2GMII_RX_RECLOCK: process(reset_i,GMII_CLK)
begin
   if reset_i = '1' then
      reg_rxdisperr    <= '0';
      reg_rxnotintable <= '0';
      reg_rxcharisk    <= '0';
      reg_rxdata       <= (others => '0');
      reg_rio_sop      <= "00";
   elsif GMII_CLK'event and GMII_CLK = '1' then
      if (rx_cycle = '1') then 
         reg_rxdisperr    <= rxdisperr_dly(1);
         reg_rxnotintable <= rxnotintable_dly(1);
         reg_rxcharisk    <= rxcharisk_dly(1);
         reg_rxdata       <= rxdata_dly(15 downto 8);
      else
         reg_rxdisperr    <= rxdisperr_dly(0);
         reg_rxnotintable <= rxnotintable_dly(0);
         reg_rxcharisk    <= rxcharisk_dly(0);
         reg_rxdata       <= rxdata_dly(7 downto 0);
      end if;
      
      reg_rio_sop <= rio_sop;
           
      if (rx_sop_sync = '1') then 
         rx_cycle <= '0';
      else
         rx_cycle <= not rx_cycle;
      end if;   
     
   end if;
end process;

-- ---------------------------------------------------------------------------
-- -- GMII_CLK to RIO_DCLK conversion
-- ---------------------------------------------------------------------------

TX_RECLOCK : process(reset_i,RIO_DCLK)
begin
   if reset_i = '1' then
   elsif RIO_DCLK'event and RIO_DCLK = '1' then
      if cycle = '1' then 
         rio_txdata_i <= reg_txdata;
      else
         rio_txdata_i <= reg_txdata(19 downto 10) & txdata_swp;
      end if;
   end if;
end process;

RX_ALIGN : process(reset_i,RIO_DCLK)
begin
   if reset_i = '1' then
      rx_realign   <= '0';
      rxdisperr    <= "00";
      rxnotintable <= "00";
      rxcharisk    <= "00";
      rxdata       <= (others => '0');
      reg_rio_rxdata       <= (others => '0');
      reg_rio_rxdisperr    <= "00";
      reg_rio_rxnotintable <= "00";
      reg_rio_rxcharisk    <= "00";
   elsif RIO_DCLK'event and RIO_DCLK = '1' then
      reg_rio_rxdata       <= rio_rxdata;
      reg_rio_rxdisperr    <= rio_rxdisperr;
      reg_rio_rxnotintable <= rio_rxnotintable;
      reg_rio_rxcharisk    <= rio_rxcharisk;   
   
      if (rx_realign = '1') then
         rxdata       <= reg_rio_rxdata(7 downto 0) & rio_rxdata(15 downto 8);
         rxdisperr    <= reg_rio_rxdisperr(0) & rio_rxdisperr(1);
         rxnotintable <= reg_rio_rxnotintable(0) & rio_rxnotintable(1);
         rxcharisk    <= reg_rio_rxcharisk(0) & rio_rxcharisk(1);
      else
         rxdata       <= rio_rxdata;
         rxdisperr    <= rio_rxdisperr;
         rxnotintable <= rio_rxnotintable;
         rxcharisk    <= rio_rxcharisk;
      end if;
      
      if (rxchariscomma = "01") then 
         rx_realign <= '1';
      elsif (rxchariscomma = "10") then 
         rx_realign <= '0';
      end if; 
   end if;
end process;

-- For simulation purposes only
rxdisperr_dly    <= rxdisperr    --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxnotintable_dly <= rxnotintable --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxcharisk_dly    <= rxcharisk    --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxdata_dly       <= rxdata       --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;

-- ---------------------------------------------------------------------------
-- -- RocketIO MGT instantion
-- ---------------------------------------------------------------------------

   GT_ETHERNET_INST : GT_ETHERNET_2
   -- synopsys translate_off
   generic map(
      CLK_COR_INSERT_IDLE_FLAG => FALSE,
      CLK_COR_KEEP_IDLE        => FALSE,
      CLK_COR_REPEAT_WAIT      => 1,
      RX_CRC_USE               => FALSE,
      RX_LOSS_OF_SYNC_FSM      => TRUE,
      RX_LOS_INVALID_INCR      => 1,
      RX_LOS_THRESHOLD         => 64,
      TERMINATION_IMP          => 75,
      SERDES_10B               => TRUE,
      TX_CRC_FORCE_VALUE       => "11010110",
      TX_CRC_USE               => FALSE,
      TX_DIFF_CTRL             => 700,
      TX_PREEMPHASIS           => 2,
      REF_CLK_V_SEL            => 1
   )
   -- synopsys translate_on
   port map (
      CONFIGENABLE            => GND,
      CONFIGIN                => GND,
      REFCLK                  => GND,
      REFCLK2                 => GND,
      BREFCLK                 => RIO_RCLK,
      BREFCLK2                => GND,
      REFCLKSEL               => GND,
      ENMCOMMAALIGN           => PWR,
      ENPCOMMAALIGN           => PWR,
      LOOPBACK(1 downto 0)    => LOOPBACK(1 downto 0),
      POWERDOWN               => GND,
      -- TX --
      TXRESET                 => reset_i,
      TXUSRCLK                => RIO_DCLK,
      TXUSRCLK2               => RIO_DCLK,
      TXBYPASS8B10B           => "00", --"11",
      TXDATA(7 downto 0)      => rio_txdata(7 downto 0),
      TXDATA(15 downto 8)     => rio_txdata(17 downto 10),
      TXCHARDISPMODE(0)       => gnd,
      TXCHARDISPMODE(1)       => gnd,
      TXCHARDISPVAL(0)        => gnd,
      TXCHARDISPVAL(1)        => gnd,
      TXCHARISK(0)            => rio_txdata(8), 
      TXCHARISK(1)            => rio_txdata(18),
      TXINHIBIT               => GND,
      TXPOLARITY              => TXPOLARITY,
      TXFORCECRCERR           => GND,
      TXBUFERR                => open,
      TXKERR                  => open,
      TXRUNDISP               => open,
      -- RX --
      RXRESET                 => reset_i,
      RXPOLARITY              => RXPOLARITY,
      RXUSRCLK                => RIO_DCLK,
      RXUSRCLK2               => RIO_DCLK,
      RXDATA                  => rio_rxdata,
      RXCHARISK               => rio_rxcharisk,
      RXDISPERR               => rio_rxdisperr,
      RXLOSSOFSYNC(1 downto 0)=> rxlossofsync(1 downto 0),
      RXNOTINTABLE            => rio_rxnotintable,
      RXBUFSTATUS             => open,
      RXCHARISCOMMA           => rxchariscomma,
      RXCLKCORCNT             => open,
      RXCOMMADET              => open,
      RXREALIGN               => open,
      RXRECCLK                => rxclk,
      RXRUNDISP               => open,
      -- RIO FPGA pads
      TXN                     => TXN,
      TXP                     => TXP,
      RXN                     => RXN,
      RXP                     => RXP
   );

GMII_RXER  <= reg_rxer;
GMII_RXD   <= reg_rxd(7 downto 0);
GMII_RXDV  <= reg_rxdv;
RXSYNCLOSS <= rxlossofsync(1);

-- -------------------------------------------------------------
-- Send ACK logic

config_present <= '1' when ((rxcharisk_dly= "10") and (rxdata_dly(7 downto 0) = K_C1) and (rxdata_dly(15 downto 8) = K28p5)) or 
                           ((rxcharisk_dly= "10") and (rxdata_dly(7 downto 0) = K_C2) and (rxdata_dly(15 downto 8) = K28p5)) else
                  '0';
process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      reg_config_present <= '0';
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      reg_config_present <= config_present;
   end if;
end process;

cnt_sndack_rst <= '1' when cnt_sndack = "11" else
                  '0';
process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      reg_sndack <= '0';
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (cnt_sndack_rst = '1') then
         reg_sndack <= '0';
      elsif (config_present = '1') then
         reg_sndack <= '1';
      end if;
   end if;
end process;

process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      cnt_sndack <= (others => '0');
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (reg_sndack = '1') then
         cnt_sndack <= cnt_sndack + 1;
      end if;
   end if;
end process;

rio_txdata <= rio_txdata_i;
--rio_txdata <= rio_txdata_i when reg_sndack = '0' else
--              sndack_data;

sndack_data(7 downto 0) <= K_C1 when cnt_sndack = "00" else
                           X"40" when cnt_sndack = "01" else
                           K_C2 when cnt_sndack = "10" else
                           X"40";
sndack_data(17 downto 10) <= k28p5 when cnt_sndack = "00" else
                             X"01" when cnt_sndack = "01" else
                             k28p5 when cnt_sndack = "10" else
                             X"01";
sndack_data(8) <= '0';
sndack_data(9) <= '0';
sndack_data(18) <= '1' when cnt_sndack = "00" else
                   '0' when cnt_sndack = "01" else
                   '1' when cnt_sndack = "10" else
                   '0';
sndack_data(19) <= '0';

-- -------------------------------------------------------------
-- PHY status port mapping

-- reg_phystatus
process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      reg_phystatus <= (others => '0');
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (reg_config_present = '1') then
         reg_phystatus <= rxdata_dly;
      end if;
   end if;
end process;

LINK_STATUS <= reg_phystatus(7);
DUPLEX_MODE <= reg_phystatus(4);
SPEED       <= reg_phystatus(3 downto 2);
SGMII       <= reg_phystatus(8);

-- -------------------------------------------------------------
-- DEBUG
-- -------------------------------------------------------------

LBCONN_MEM_U : entity work.lbconn_mem
generic map(
   BASE           => BASE,  -- base address
   ADDR_WIDTH     => 4 -- address bus width
)
port map(
   DATA_OUT => lb_do,
   DATA_IN  => lb_di,
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
lb_drdy <= '1';
lb_di   <= x"0000";


counter_rst <= '1' when lb_addr = x"0" and lb_rw = '1' and lb_en = '1' else
               '0';

-- cnt_bp counter : 
process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      cnt_bp <= (others => '0');
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (counter_rst = '1') then
         cnt_bp <= X"00000000";
      elsif (cnt_bp_ce='1' and not_idle = '1') then
         cnt_bp <= cnt_bp + 1;
      end if;
   end if;
end process;

process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      cnt_bp_ce <= '1';
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (counter_rst = '1') then
         cnt_bp_ce <= '1';
      elsif (cnt_bp = (BUFFER_SIZE-1)) then
         cnt_bp_ce <= '0';
      end if;
   end if;
end process;

monitored_bus <= rxcharisk_dly & rxdata_dly;
start_trig  <= '1' when ((rxcharisk_dly(0) = '1') and (rxdata_dly(7 downto 0) = K_SOP)) or
                        ((rxcharisk_dly(1) = '1') and (rxdata_dly(15 downto 8) = K_SOP)) else
               '0';

stop_trig  <= '1' when ((rxcharisk_dly(0) = '1') and (rxdata_dly(7 downto 0) = K_EOP)) or
                       ((rxcharisk_dly(1) = '1') and (rxdata_dly(15 downto 8) = K_EOP)) else
              '0';
not_idle   <= '1' when not ((rxcharisk_dly= "10") and (rxdata_dly(7 downto 0) = X"50") and (rxdata_dly(15 downto 8) = K28p5)) else
              '0';
reg_last_config_we <= '1' when (reg_last_config /= monitored_bus) and (reg_config_present = '1') else
                      '0';

--process(RESET, RIO_DCLK)
--begin
--   if (RESET = '1') then
--      reg_packet_rcv <= '0';
--   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
--      if (stop_trig = '1') then
--         reg_packet_rcv <= '0';
--      elsif (start_trig = '1') then
--         reg_packet_rcv <= '1';
--      end if;
--   end if;
--end process;

process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      reg_last_config <= (others => '0');
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      if (reg_last_config_we = '1') then
         reg_last_config <= monitored_bus;
      end if;
   end if;
end process;


process(RESET, RIO_DCLK)
begin
   if (RESET = '1') then
      reg_last_config_we_pipe <= '0';
   elsif (RIO_DCLK'event AND RIO_DCLK = '1') then
      reg_last_config_we_pipe <= reg_last_config_we;
   end if;
end process;


bp_wen <= reg_last_config_we_pipe or reg_packet_rcv;
bp_di  <= reg_last_config when reg_last_config_we_pipe = '1' else
          monitored_bus;
busprobe_u: BUSPROBE
   generic map(
       BASE             => BP_BASE,
       ADC_FREQUENCY    => 100,
       -- width of monitored bus:
       BUS_WIDTH        => MBUS_WIDTH,
       -- number of items in buffer:
       BUFFER_SIZE      => BUFFER_SIZE,
       -- Block Ram Type, only 1, 2, 4, 8, 16, 32 bits
       BRAM_TYPE        => 32
   )
   port map(
      CLK               => lbclk,
      SAMPLE_CLK        => RIO_DCLK,
      RESET             => reset_i,

      -- hardware interface
      EN                => '1',
      WEN               => not_idle, --'1',
      START_TRIGGER     => '1', --start_trig,
      STOP_TRIGGER      => '0', --stop_trig,
      TOGGLE_TRIGGER    => '0',
      MONITORED_BUS     => monitored_bus,

      -- local bus interface
      LBCLK             => lbclk,
      LBFRAME           => lbframe,
      LBHOLDA           => lbholda,
      LBAD              => lbad,
      LBAS              => lbas,
      LBRW              => lbrw,
      LBRDY             => lbrdy,
      LBLAST            => lblast
   );

end behavioral;
