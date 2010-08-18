-- rio_gmii.vhd: RocketIO to GMII interface for 1G Ethernet
-- Copyright (C) 2005 CESNET
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
-- TODO:

library ieee;
use ieee.std_logic_1164.ALL;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- synopsys translate_off
library UNISIM;
use UNISIM.Vcomponents.ALL;
-- synopsys translate_on

entity rio_gmii is
   port (
      RIO_RCLK  : in  std_logic; -- Precise reference clock for RIO, 125MHz
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
      RXSYNCLOSS: out std_logic
    );
end rio_gmii;

architecture behavioral of rio_gmii is

   constant K_SOP : std_logic_vector(7 downto 0) := X"FB";
   constant K_EOP : std_logic_vector(7 downto 0) := X"FD";
   constant K_ERR : std_logic_vector(7 downto 0) := X"FE";
   constant K_CEX : std_logic_vector(7 downto 0) := X"F7";
   constant K28p5 : std_logic_vector(7 downto 0) := X"BC";

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

   type T_AN_STATE is (IDLE, AN_CFG_WAIT, CFG_DATA, CFG_ACK);
   type T_CFG_DATA_STATE is (IDLE, C0, C1, DATA0, DATA1, C0_1, C1_1, DATA0_1, DATA1_1);
   type T_RX_MON_STATE is (IDLE, OSET, CFG_D0, CFG_D1);
   signal an_state      : t_an_state;
   signal an_next_state : t_an_state;
   signal cfg_data_state      : t_cfg_data_state;
   signal cfg_data_next_state : t_cfg_data_state;
   signal rx_mon_state        : t_rx_mon_state;
   signal rx_mon_next_state   : t_rx_mon_state;
   signal an_state_d    : std_logic_vector(3 downto 0);
   signal cfgtx_state_d : std_logic_vector(3 downto 0);

   signal GND          : std_logic;
   signal PWR          : std_logic;
   signal rst_cntr     : std_logic_vector(4 downto 0);
   signal reset_i      : std_logic;
   signal rxclk        : std_logic;
   signal cycle        : std_logic := '1';
   signal rx_cycle     : std_logic := '0';
   signal txdata_pcs   : std_logic_vector(9 downto 0);
   signal txdata_cfg   : std_logic_vector(9 downto 0);
   signal txdata       : std_logic_vector(9 downto 0);
   signal reg_txdata   : std_logic_vector(19 downto 0);
   signal rio_txdata   : std_logic_vector(19 downto 0);
   signal rxdata       : std_logic_vector(15 downto 0);
   signal rxdisperr    : std_logic_vector(1 downto 0);
   signal rxlossofsync : std_logic_vector(1 downto 0);
   signal rxnotintable : std_logic_vector(1 downto 0);
   signal rxcharisk    : std_logic_vector(1 downto 0);
   signal rxchariscomma: std_logic_vector(1 downto 0);
   signal rxdata_dly       : std_logic_vector(15 downto 0);
   signal rxdisperr_dly    : std_logic_vector(1 downto 0);
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
   signal rx_dchar_val : std_logic;
   signal rx_idle      : std_logic;
   signal rx_idle_det  : std_logic;
   signal rx_err_det   : std_logic;
   signal rx_sop       : std_logic;
   signal rx_eop       : std_logic;
   signal reg_rx_eop   : std_logic;
   signal rx_err       : std_logic; --
   signal rx_cex       : std_logic; -- Carrier extend
   signal rx_ferr      : std_logic; --
   signal rx_eeop      : std_logic; --
   signal rx_fc        : std_logic; --
   signal rx_cfg_det   : std_logic; --
   signal rx_set_err   : std_logic; -- 
   signal rx_set_idle  : std_logic; -- 
   signal rx_set_cfg   : std_logic; -- 
   signal rx_clr_cfg   : std_logic; -- 
   signal rx_data_mx   : std_logic_vector(7 downto 0);
   signal reg_rxer     : std_logic;
   signal reg_rxd      : std_logic_vector(7 downto 0);
   signal reg_rxdv     : std_logic;
   signal rx_realign   : std_logic;
   signal gmii_rx_dv   : std_logic;
   signal reg_gmii_txd : std_logic_vector(7 downto 0) := (others => '0');
   signal reg_gmii_txdv: std_logic;

   -- Auto-negotiation
   signal rx_cfg_cntr  : std_logic_vector(1 downto 0) := "00"; --
   signal rx_cfg_d0    : std_logic := '0'; --
   signal rx_cfg_d1    : std_logic := '0'; --
   signal rx_config_reg: std_logic_vector(15 downto 0):= (others => '0');
   signal rx_cfgr_zero : std_logic; --
   signal tx_cfgr_wen  : std_logic; --
   signal tx_config_reg: std_logic_vector(15 downto 0); --
   signal tx_config_i  : std_logic_vector(15 downto 0); --
   signal an_start     : std_logic;
   signal an_valid     : std_logic;
   signal an_valid_rise: std_logic;
   signal reg_an_valid : std_logic;
   signal tx_cfg       : std_logic; --
   signal tx_sel_cfg   : std_logic; --

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

      DATA_8    => txdata_pcs(7 downto 0),
      DATA_8_K  => txdata_pcs(8),
      DATA_10   => open        -- 10b output data
   );

   txdata_pcs(9) <= '0';

   txdata <= txdata_cfg when tx_sel_cfg = '1' else
             txdata_pcs;

   TXDATA_REG : process(reset_i,GMII_CLK)
   begin
      if reset_i = '1' then
         reg_txdata    <= "01" & K28p5 & "00" & X"50"; -- IDLE pattern
         cycle         <= '1'; -- !! Do not change
         reg_gmii_txdv <= '0';
      elsif GMII_CLK'event and GMII_CLK = '1' then
         cycle          <= not cycle;
         reg_gmii_txd   <= GMII_TXD;
         reg_gmii_txdv  <= GMII_TXEN;
         if (cycle = '1') then
            reg_txdata(19 downto 10) <= txdata;
         else
            reg_txdata( 9 downto  0) <= txdata;
         end if;
      end if;
   end process;

-- ---------------------------------------------------------------------------
-- -- RX, SFP to GMII conversion --
-- ---------------------------------------------------------------------------

RX_LINE_FLAGS: process(GMII_CLK)
begin
   if GMII_CLK'event and GMII_CLK = '1' then
      -- /CFG/ ordered set counter 
      if (rx_set_err = '1') or (rx_set_idle = '1') or (rx_clr_cfg = '1') then
         rx_cfg_cntr <= (others => '0');
      elsif (rx_cfg_cntr /= "11") and (rx_cfg_d1 = '1') then
         rx_cfg_cntr <= rx_cfg_cntr + 1;
      end if;
      -- RX configuration flag
      if (rx_set_err = '1') or (rx_set_idle = '1') or (rx_clr_cfg = '1') then
         rx_cfg_det    <= '0';
      elsif (rx_cfg_d1 = '1') then
         rx_cfg_det    <= '1';
      end if;
      -- RX idle (line OK) flag
      if (rx_set_err = '1') or (rx_set_cfg = '1') then
         rx_idle_det   <= '0';
      elsif (rx_set_idle = '1') then
         rx_idle_det   <= '1';
      end if;
      -- RX Error flag
      if (rx_set_cfg = '1') or (rx_set_idle = '1') then
         rx_err_det   <= '0';
      elsif (rx_set_idle = '1') then
         rx_err_det   <= '1';
      end if;
   end if;
end process;

-- FSM monitors RX line status
RX_MONITOR: process(rx_mon_state, rx_dchar_val, rx_kchar_val, rx_char_val)
begin
   rx_cfg_d0   <= '0';
   rx_cfg_d1   <= '0';
   rx_set_err  <= '0';
   rx_set_idle <= '0';
   rx_set_cfg  <= '0';
   rx_clr_cfg  <= '0';
   case rx_mon_state is
   
      when IDLE =>
         if rx_char_val = '0' then 
            rx_set_err <= '1'; -- Set Error flag
         end if;
         if rx_idle = '1' then -- K28p5 kchar detected
            rx_mon_next_state <= OSET;
         else
            rx_clr_cfg <= '1';
            rx_mon_next_state <= IDLE;
         end if;
      -- Ordered set -- Char 1
      when OSET =>
         if (rx_dchar_val = '1') then
            if (reg_rxdata = X"42") or (reg_rxdata = X"B5") then
               rx_mon_next_state <= CFG_D0; -- Configuration
               rx_set_cfg <= '1';    -- Set Cfg flag
            elsif (reg_rxdata = X"C5") or (reg_rxdata = X"50") then
               rx_mon_next_state <= IDLE; -- Idle
               rx_set_idle <= '1'; -- Set Idle flag
            else
               rx_mon_next_state <= IDLE; -- Another char is not valid
               rx_set_err  <= '1'; -- Set Idle flag
            end if;
         else
            rx_mon_next_state <= IDLE;
            rx_set_err <= '1';
         end if;
      -- Configuration -- Data 0
      when CFG_D0 =>
         if rx_dchar_val = '1' then
            rx_cfg_d0 <= '1';
            rx_mon_next_state <= CFG_D1;
         else
            rx_mon_next_state <= IDLE;
            rx_set_err <= '1'; -- Set Error flag
         end if;
      -- Configuration -- Data 1
      when CFG_D1 =>
         rx_mon_next_state <= IDLE;
         if rx_dchar_val = '1' then
            rx_cfg_d1 <= '1';
         else
            rx_set_err <= '1'; -- Set Error flag
         end if;
      end case;
end process;

RQ_MON_SEQ: process(reset_i, GMII_CLK)
begin
   if reset_i = '1' then
      rx_mon_state      <= IDLE;
   elsif GMII_CLK'event and GMII_CLK = '1' then
      rx_mon_state <= rx_mon_next_state;
   end if;
end process;

rx_char_val  <= (not reg_rxnotintable) and (not reg_rxdisperr);
rx_kchar_val <= reg_rxcharisk and rx_char_val;
rx_dchar_val <= (not reg_rxcharisk) and rx_char_val;

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
   if RIO_DCLK'event and RIO_DCLK = '1' then
      if cycle = '1' then
         rio_txdata <= reg_txdata;
      else
         rio_txdata <= reg_txdata(19 downto 10) & txdata;
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

-- ----------------------------------------------------------------------------
-- Auto-negotiation -----------------------------------------------------------
-- ----------------------------------------------------------------------------

STORE_RX_CFG: process(GMII_CLK)
begin
   if GMII_CLK'event and GMII_CLK = '1' then
      if (an_valid_rise = '1') then 
         rx_config_reg <= (others => '0');
      elsif (an_valid = '1') then
         if (rx_cfg_d0 = '1') then
            rx_config_reg( 7 downto 0) <= reg_rxdata;
         end if;
         if (rx_cfg_d1 = '1') then
            rx_config_reg(15 downto 8) <= reg_rxdata;
         end if;
      end if;
      reg_an_valid <= an_valid;
      --
      if (rx_config_reg = X"0000") then
         rx_cfgr_zero  <= '1';
      else
         rx_cfgr_zero  <= '0';
      end if;
   end if;
end process;

an_valid      <= '1' when (rx_cfg_det = '1') and (rx_cfg_cntr = "11") else '0';
an_valid_rise <= an_valid and (not reg_an_valid);
an_start      <= an_valid and rx_cfgr_zero;
                
AN_FSM: process(an_state, an_start, rx_idle_det, rx_config_reg, rx_cfgr_zero,
                an_valid)
begin
   tx_config_i   <= (others => '0');
   tx_cfg        <= '0';
   an_state_d    <= X"0";

   case an_state is
      when IDLE =>
         an_state_d    <= X"1";
         if an_start = '1' then
            an_next_state <= AN_CFG_WAIT;
         else
            an_next_state <= IDLE;
         end if;

      -- Wait for AN base register from partner
      when AN_CFG_WAIT =>
        an_state_d    <= X"2";
        tx_cfg        <= '1';
        tx_config_i <= "0000000001100000"; -- X"0060" = HD & FD
        if (an_valid = '0') then
           an_next_state <= IDLE;
        elsif (rx_cfgr_zero = '0') then -- Link partner config reg received
           if (rx_config_reg(14) = '1') then -- ACK received
              an_next_state <= CFG_ACK;
           else
              an_next_state <= CFG_DATA;
           end if;
        else
           an_next_state <= AN_CFG_WAIT;
        end if;

      -- Received link partner base reg, generate ACK and wait for acknowledge
      when CFG_DATA =>
         an_state_d    <= X"3";
         tx_cfg        <= '1';
         -- NP & ACK & RF2 & RF1 & 000 & PS2 & PS1 & HD & FD &
         tx_config_i <= "0100000001100000"; -- X"4060" = Ack & FD & HD
         if (an_valid = '0') then 
            an_state_d    <= X"A";
            an_next_state <= IDLE;
         elsif (rx_config_reg(14) = '1') then
            an_next_state <= CFG_ACK;
         elsif (an_start = '1') then
            an_next_state <= AN_CFG_WAIT;
         else
            an_next_state <= CFG_DATA;
         end if;

      -- Received acknowledge from link partner, generate ACK 
      when CFG_ACK =>
         an_state_d    <= X"4";
         tx_cfg        <= '1';
         -- NP&ACK&RF2&RF1  &  000&PS2 &  PS1&HD&FD&'0'  &  "0000"
         tx_config_i <= "0100000001100000"; -- X"4060" = Ack & FD & HD
         if (an_valid = '0') then
            an_next_state <= IDLE;
         elsif (an_start = '1') then
            an_next_state <= AN_CFG_WAIT;
            an_state_d    <= X"B";
         else
            an_next_state <= CFG_ACK;
         end if;

   end case;
end process;

RX_CFG_REG : process(GMII_CLK)
begin
   if GMII_CLK'event and GMII_CLK = '1' then
      if tx_cfgr_wen = '1' then
         tx_config_reg <= tx_config_i;
      end if;
   end if;
end process;

-- Generate /C/ (configuration) ordered set ----------------------------------
CFG_DATA_FSM : process(cfg_data_state, tx_cfg, tx_config_reg)
begin
   cfgtx_state_d <= X"0";
   tx_sel_cfg    <= '0';
   tx_cfgr_wen   <= '0';
   case cfg_data_state is

      -- Idle or first /C1/ ordered set
      when IDLE => 
         cfgtx_state_d <= X"0";
         txdata_cfg <= "01" & K28p5;
         if (tx_cfg = '1') and (txdata_pcs(8) = '1') then -- Sychronize K28p5 with PCS
            tx_sel_cfg  <= '1';
            tx_cfgr_wen <= '1';
            cfg_data_next_state <= C0_1;
         else
            cfg_data_next_state <= IDLE;
         end if;
         
      -- /C1/ ordered set
      when C0 =>
         cfgtx_state_d <= X"1";
         txdata_cfg <= "01" & K28p5;
         tx_sel_cfg  <= '1';
         tx_cfgr_wen <= '1';
         cfg_data_next_state <= C0_1;
         
      when C0_1 =>
         cfgtx_state_d <= X"2";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & X"B5"; -- /C1/ ordered set
         cfg_data_next_state <= DATA0;

      -- /C2/ ordered set
      when C1 =>
         cfgtx_state_d <= X"3";
         txdata_cfg <= "01" & K28p5;
         tx_sel_cfg <= '1';
         cfg_data_next_state <= C1_1;
      when C1_1 =>
         cfgtx_state_d <= X"4";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & X"42";
         cfg_data_next_state <= DATA1;

      -- tx_data_reg
      when DATA0 =>
         cfgtx_state_d <= X"5";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg( 7 downto 0);
         cfg_data_next_state <= DATA0_1;
      when DATA0_1 =>
         cfgtx_state_d <= X"6";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg(15 downto 8);
         cfg_data_next_state <= C1;

      when DATA1 =>
         cfgtx_state_d <= X"7";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg( 7 downto 0);
         cfg_data_next_state <= DATA1_1;
         
      when DATA1_1 =>
         cfgtx_state_d <= X"8";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg(15 downto 8);
         if (tx_cfg = '1') then
            cfg_data_next_state <= C0;
         else
            cfg_data_next_state <= IDLE;
         end if;

   end case;
end process;

AN_FSM_SEQ : process(GMII_CLK, reset_i)
begin
   if reset_i = '1' then
      an_state       <= IDLE;
      cfg_data_state <= IDLE;
   elsif GMII_CLK'event and GMII_CLK = '1' then
      an_state       <= an_next_state;
      cfg_data_state <= cfg_data_next_state;
   end if;
end process;

end behavioral;
