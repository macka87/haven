-- rio_gmii.vhd: RocketIO to GMII interface for 1G Ethernet on ComboV2
-- Copyright (C) 2009 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

entity rio_gmii_cv2 is
   port (
      -- Reference clock signal - 125 MHz
      REFCLK         : in  std_logic;
      -- Global reset
      RESET          : in  std_logic;
      
      -- GMII interface
      GMII_TXD       : in  std_logic_vector(7 downto 0);
      GMII_TX_EN     : in  std_logic;
      GMII_TX_ER     : in  std_logic;
      GMII_TX_CLK    : in  std_logic;
      GMII_RXD       : out std_logic_vector(7 downto 0);
      GMII_RX_DV     : out std_logic;
      GMII_RX_ER     : out std_logic;
      GMII_RX_CLK    : out std_logic;
      MII_TX_CLK     : out std_logic;
      GMII_COL       : out std_logic;
      GMII_CRS       : out std_logic;

      -- GTP interface
      ENCOMMAALIGN   : out std_logic;
      LOOPBACK       : out std_logic;
      RX_RESET       : out std_logic;
      TX_CHARDISPMODE : out std_logic;
      TX_CHARDISPVAL  : out std_logic;
      TX_CHARISK      : out std_logic;
      TX_DATA         : out std_logic_vector(7 downto 0);
      TX_RESET        : out std_logic;
      RX_CHARISCOMMA  : in  std_logic;
      RX_CHARISK      : in  std_logic;
      RX_DATA         : in  std_logic_vector(7 downto 0);
      RX_DISPERR      : in  std_logic;
      RX_NOTINTABLE   : in  std_logic;

      -- Link status
      RXSYNCLOSS     : out std_logic -- Indicates loss of synchronization
    );
end rio_gmii_cv2;

architecture behavioral of rio_gmii_cv2 is

   -- -------------------------------------------------------------------------
   --                          Constant Declarations
   -- -------------------------------------------------------------------------
   -- Constant values on RocketIO Serial Transceiver interface
   constant EN_COMMA_ALIGN_CONST    : std_logic := '1';
   constant EN_LOOPBACK_CONST       : std_logic := '0';
   constant TX_CHARDISPMODE_CONST   : std_logic := '0';
   constant TX_CHARDISPVAL_CONST    : std_logic := '0';

   -- Special codegroups
   constant K_SOP : std_logic_vector(7 downto 0) := X"FB";
   constant K_EOP : std_logic_vector(7 downto 0) := X"FD";
   constant K_ERR : std_logic_vector(7 downto 0) := X"FE";
   constant K_CEX : std_logic_vector(7 downto 0) := X"F7";
   constant K28p5 : std_logic_vector(7 downto 0) := X"BC";

   -- -------------------------------------------------------------------------
   --                          Type Declarations
   -- -------------------------------------------------------------------------
   
   type T_AN_STATE is (IDLE, AN_CFG_WAIT, CFG_DATA, CFG_ACK);
   type T_CFG_DATA_STATE is (IDLE, C0, C1, DATA0, DATA1, C0_1, C1_1, DATA0_1, DATA1_1);
   type T_RX_MON_STATE is (IDLE, OSET, CFG_D0, CFG_D1);
   
   -- -------------------------------------------------------------------------
   --                          Signal Declarations
   -- -------------------------------------------------------------------------
   -- Reset and other auxiliary signals
   signal GND                 : std_logic;
   signal PWR                 : std_logic;
   signal reset_i             : std_logic;
   signal rst_cntr            : std_logic_vector(4 downto 0);
   signal cycle               : std_logic := '0';
   
   ----- RX direction -----
   -- RX signals from RocketIO Transceivers
   signal rio_rxdata          : std_logic_vector(7 downto 0);
   signal rio_rxdisperr       : std_logic;
   signal rio_rxnotintable    : std_logic;
   signal rio_rxcharisk       : std_logic;
   
   -- RX signals - 1st stage
   signal rxdata              : std_logic_vector(7 downto 0);
   signal rxdisperr           : std_logic;
   signal rxnotintable        : std_logic;
   signal rxcharisk           : std_logic;
   signal rxlossofsync        : std_logic;
   signal rxchariscomma       : std_logic;
   
   -- Delayed RX signals (because of simulation)
   signal rxdata_dly          : std_logic_vector(7 downto 0);
   signal rxdisperr_dly       : std_logic;
   signal rxnotintable_dly    : std_logic;
   signal rxcharisk_dly       : std_logic;
   
   -- RX signals - 2nd stage
   signal reg_rxdata          : std_logic_vector(7 downto 0);
   signal reg_rxdisperr       : std_logic;
   signal reg_rxnotintable    : std_logic;
   signal reg_rxcharisk       : std_logic;
   
   -- Chosen data in RX
   signal rx_data_mx          : std_logic_vector(7 downto 0);
   
   -- GMII RX output registers
   signal reg_rxd             : std_logic_vector(7 downto 0);
   signal reg_rxdv            : std_logic;
   signal reg_rxer            : std_logic;
   
   -- Type of codegroup in RX
   signal rx_char_val         : std_logic;
   signal rx_kchar_val        : std_logic;
   signal rx_dchar_val        : std_logic;

   -- Possible K codegroups in RX
   signal rx_idle             : std_logic;
   signal rx_sop              : std_logic;
   signal rx_eop              : std_logic;
   signal rx_err              : std_logic;
   signal rx_cex              : std_logic; -- Carrier extend

   -- RX line flags
   signal rx_cfg_det          : std_logic;
   signal rx_err_det          : std_logic;
   signal rx_idle_det         : std_logic;

   -- RX monitor FSM states
   signal rx_mon_state        : t_rx_mon_state;
   signal rx_mon_next_state   : t_rx_mon_state;

   -- RX line status indicators
   signal rx_set_err          : std_logic;
   signal rx_set_idle         : std_logic;
   signal rx_set_cfg          : std_logic;
   signal rx_clr_cfg          : std_logic;
   
   -- Special situations on RX line
   signal rx_fc               : std_logic;
   signal rx_ferr             : std_logic;
   signal rx_eeop             : std_logic;
   
   -- GMII RX control signals
   signal gmii_rxdv           : std_logic;
   signal reg_rx_eop          : std_logic;
   
   ----- TX direction -----
   -- GMII TX input registers
   signal reg_gmii_txd        : std_logic_vector(7 downto 0) := (others => '0');
   signal reg_gmii_txdv       : std_logic;
   
   -- Encoded GMII TX data
   signal txdata_pcs          : std_logic_vector(9 downto 0);
   
   -- Configuration TX data
   signal txdata_cfg          : std_logic_vector(9 downto 0);
   
   -- PCS or CFG data in TX
   signal txdata              : std_logic_vector(9 downto 0);
   
   -- TX data register (already multiplexed PCS or CFG)
   signal reg_txdata          : std_logic_vector(9 downto 0);
   
   -- TX data to RocketIO Transceiver
   signal rio_txdata          : std_logic_vector(9 downto 0);

   ----- Auto-negotiation -----
   -- RX Configuration ordered set counter
   signal rx_cfg_cntr         : std_logic_vector(1 downto 0) := "00";

   -- RX Configuration indicators
   signal rx_cfg_d0           : std_logic := '0';
   signal rx_cfg_d1           : std_logic := '0';
   
   -- RX Configuration register
   signal rx_config_reg       : std_logic_vector(15 downto 0):= (others => '0');

   -- Empty RX configuration register indicator
   signal rx_cfgr_zero        : std_logic;
   
   -- TX Configuration indicator
   signal tx_cfg              : std_logic;
   
   -- TX configuration selector
   signal tx_sel_cfg          : std_logic;

   -- TX configuration register and some auxiliary registers
   signal tx_config_reg       : std_logic_vector(15 downto 0);
   signal tx_config_i         : std_logic_vector(15 downto 0);
   signal tx_cfgr_wen         : std_logic;
   
   -- Auto-Negotiation auxiliary signals
   signal an_start            : std_logic;
   signal an_valid            : std_logic;
   signal an_valid_rise       : std_logic;
   signal reg_an_valid        : std_logic;
   
   -- Auto-Negotiation FSM states
   signal an_state            : t_an_state;
   signal an_next_state       : t_an_state;
   signal cfg_data_state      : t_cfg_data_state;
   signal cfg_data_next_state : t_cfg_data_state;

   -- FSMs state debug info
   signal an_state_d          : std_logic_vector(3 downto 0);
   signal cfgtx_state_d       : std_logic_vector(3 downto 0);
   
   
begin

-------------------------------------------------------------------------------
-- Main code --
-------------------------------------------------------------------------------

GND <= '0';
PWR <= '1';

POWERUP_RESET: process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (RESET = '1') then
         rst_cntr <= (others => '0');
      else
         rst_cntr <= rst_cntr + 1;
      end if;

      if (RESET = '1') then
         reset_i <= '1';
      elsif (rst_cntr(rst_cntr'high) = '1') then
         reset_i <= '0';
      end if;
   end if;
end process;


-------------------------------------------------------------------------------
-- Output signals to EMAC  --
-------------------------------------------------------------------------------

GMII_RXD          <= reg_rxd;
GMII_RX_DV        <= reg_rxdv;
GMII_RX_ER        <= reg_rxer;
GMII_RX_CLK       <= REFCLK;
MII_TX_CLK        <= REFCLK;
GMII_COL          <= '0';
GMII_CRS          <= '1';


-------------------------------------------------------------------------------
-- Input signals from RocketIO transceiver  --
-------------------------------------------------------------------------------

rxchariscomma     <= RX_CHARISCOMMA;
rio_rxcharisk     <= RX_CHARISK;
rio_rxdata        <= RX_DATA;
rio_rxdisperr     <= RX_DISPERR;
rio_rxnotintable  <= RX_NOTINTABLE;


-------------------------------------------------------------------------------
-- Output signals to RocketIO transceiver  --
-------------------------------------------------------------------------------

ENCOMMAALIGN      <= EN_COMMA_ALIGN_CONST;
LOOPBACK          <= EN_LOOPBACK_CONST;
RX_RESET          <= reset_i;
TX_CHARDISPMODE    <= TX_CHARDISPMODE_CONST;
TX_CHARDISPVAL     <= TX_CHARDISPVAL_CONST;
TX_CHARISK         <= rio_txdata(8);
TX_DATA            <= rio_txdata(7 downto 0);
TX_RESET           <= reset_i;


-------------------------------------------------------------------------------
-- Other output signals  --
-------------------------------------------------------------------------------

RXSYNCLOSS  <= rxlossofsync;

-------------------------------------------------------------------------------
-- TX, GMII to SFP conversion --
-------------------------------------------------------------------------------

-- TX data PCS and 8b/10b conversion
GMII2SFP_PCS : entity work.pcs_mx_out
port map(
   RESET     => reset_i,         -- global reset
   TX_CLK    => GMII_TX_CLK,     -- 10b output clock
   TX_D      => reg_gmii_txd,    -- GMII 8b data
   TX_EN     => reg_gmii_txdv,   -- GMII data valid
   TX_ERR    => GMII_TX_ER,      -- GMII data error

   DATA_8    => txdata_pcs(7 downto 0),
   DATA_8_K  => txdata_pcs(8),
   DATA_10   => open             -- 10b output data
);

txdata_pcs(9) <= '0';

txdata <= txdata_cfg when tx_sel_cfg = '1' else
          txdata_pcs;

TXDATA_REG : process(reset_i, cycle, GMII_TX_CLK)
begin
   if (reset_i = '1') then
      -- IDLE pattern
      if (cycle = '0') then
         reg_txdata  <= "01" & K28p5;
      else
         reg_txdata  <= "00" & X"50";
      end if;
      reg_gmii_txdv  <= '0';
   elsif (GMII_TX_CLK'event and GMII_TX_CLK = '1') then
      reg_gmii_txd   <= GMII_TXD;
      reg_gmii_txdv  <= GMII_TX_EN;
      reg_txdata     <= txdata;
   end if;
end process;
   
CYCLE_REG : process (reset_i, GMII_TX_CLK)
begin
   if (reset_i = '1') then
      if (GMII_TX_CLK'event and GMII_TX_CLK = '1') then
         cycle <= not cycle;
      end if;
   else
      cycle <= '0';
   end if;
end process;


-------------------------------------------------------------------------------
-- RX, SFP to GMII conversion --
-------------------------------------------------------------------------------

RX_LINE_FLAGS: process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      -- /CFG/ ordered set counter 
      if ((rx_set_err = '1') or (rx_set_idle = '1') or (rx_clr_cfg = '1')) then
         rx_cfg_cntr <= (others => '0');
      elsif ((rx_cfg_cntr /= "11") and (rx_cfg_d1 = '1')) then
         rx_cfg_cntr <= rx_cfg_cntr + 1;
      end if;
      -- RX configuration flag
      if ((rx_set_err = '1') or (rx_set_idle = '1') or (rx_clr_cfg = '1')) then
         rx_cfg_det    <= '0';
      elsif (rx_cfg_d1 = '1') then
         rx_cfg_det    <= '1';
      end if;
      -- RX idle (line OK) flag
      if ((rx_set_err = '1') or (rx_set_cfg = '1')) then
         rx_idle_det   <= '0';
      elsif (rx_set_idle = '1') then
         rx_idle_det   <= '1';
      end if;
      -- RX Error flag
      if ((rx_set_cfg = '1') or (rx_set_idle = '1')) then
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
         if (rx_char_val = '0') then
            rx_set_err        <= '1';  -- Set Error flag
         end if;
         if (rx_idle = '1') then       -- K28p5 kchar detected
            rx_mon_next_state <= OSET;
         else
            rx_clr_cfg        <= '1';
            rx_mon_next_state <= IDLE;
         end if;
         
      -- Ordered set -- Char 1
      when OSET =>
         if (rx_dchar_val = '1') then
            if ((reg_rxdata = X"42") or (reg_rxdata = X"B5")) then
               rx_mon_next_state <= CFG_D0;  -- Configuration
               rx_set_cfg        <= '1';     -- Set Cfg flag
            elsif ((reg_rxdata = X"C5") or (reg_rxdata = X"50")) then
               rx_mon_next_state <= IDLE;    -- Idle
               rx_set_idle       <= '1';     -- Set Idle flag
            else
               rx_mon_next_state <= IDLE;    -- Another char is not valid
               rx_set_err        <= '1';     -- Set Idle flag
            end if;
         else
            rx_mon_next_state    <= IDLE;
            rx_set_err           <= '1';
         end if;

      -- Configuration -- Data 0
      when CFG_D0 =>
         if (rx_dchar_val = '1') then
            rx_cfg_d0         <= '1';
            rx_mon_next_state <= CFG_D1;
         else
            rx_mon_next_state <= IDLE;
            rx_set_err        <= '1';  -- Set Error flag
         end if;
         
      -- Configuration -- Data 1
      when CFG_D1 =>
         rx_mon_next_state <= IDLE;
         if (rx_dchar_val = '1') then
            rx_cfg_d1   <= '1';
         else
            rx_set_err  <= '1';  -- Set Error flag
         end if;

   end case;
end process;

RQ_MON_SEQ: process(reset_i, REFCLK)
begin
   if (reset_i = '1') then
      rx_mon_state   <= IDLE;
   elsif (REFCLK'event and REFCLK = '1') then
      rx_mon_state   <= rx_mon_next_state;
   end if;
end process;

rx_char_val  <= (not reg_rxnotintable) and (not reg_rxdisperr);
rx_kchar_val <= reg_rxcharisk and rx_char_val;
rx_dchar_val <= (not reg_rxcharisk) and rx_char_val;

rx_idle <= '1' when ((rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K28p5))
           else '0';
-- Start of frame
rx_sop  <= '1' when ((rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_SOP))
           else '0';
-- End of frame
rx_eop  <= '1' when ((rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_EOP))
           else '0';
-- Error propagation
rx_err  <= '1' when ((rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_ERR))
           else '0';
-- Carrier extend
rx_cex  <= '1' when ((rx_kchar_val = '1') and (reg_rxdata(7 downto 0) = K_CEX)
                    and (reg_rx_eop = '0'))
           else '0';
           
-- False carrier
rx_fc   <= (not gmii_rxdv) and (not reg_rx_eop) and
           (rx_kchar_val and (not rx_idle) and (not rx_sop) and (not rx_cex));
-- Error inside the frame
rx_ferr <= gmii_rxdv and
           ((rx_kchar_val and (not rx_eop)) or (not rx_char_val));
-- Early end of frame
rx_eeop <= gmii_rxdv and (rx_idle or rx_cex);

rx_data_mx <= X"55" when rx_sop = '1' else
              X"0F" when rx_cex = '1' else
              X"0E" when rx_fc = '1'  else
              reg_rxdata;

GMII_RX_GEN : process(reset_i,REFCLK)
begin
   if (reset_i = '1') then
      gmii_rxdv <= '0';
      reg_rx_eop <= '0';
   elsif (REFCLK'event and REFCLK = '1') then
      if (rx_sop = '1') then
         gmii_rxdv <= '1';
      elsif ((rx_eop = '1') or (rx_eeop = '1')) then
         gmii_rxdv <= '0';
      end if;
      reg_rx_eop <= rx_eop;
   end if;
end process;

GMII_OUT_REGS: process(reset_i,REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if ((reset_i = '1') or (rxlossofsync = '1')) then
         reg_rxer <= '0';
         reg_rxd  <= (others => '0');
         reg_rxdv <= '0';
      else
         reg_rxer <= rx_fc or rx_err or rx_ferr or rx_eeop or rx_cex;
         reg_rxd  <= rx_data_mx;
         reg_rxdv <= (rx_sop or gmii_rxdv) and (not rx_eop);
      end if;
   end if;
end process;

RIO2GMII_RX_RECLOCK: process(reset_i,REFCLK)
begin
   if (reset_i = '1') then
      reg_rxdata        <= (others => '0');
      reg_rxdisperr     <= '0';
      reg_rxnotintable  <= '0';
      reg_rxcharisk     <= '0';
   elsif (REFCLK'event and REFCLK = '1') then
      reg_rxdata        <= rxdata_dly;
      reg_rxdisperr     <= rxdisperr_dly;
      reg_rxnotintable  <= rxnotintable_dly;
      reg_rxcharisk     <= rxcharisk_dly;
   end if;
end process;


-- ----------------------------------------------------------------------------
-- -- GMII_CLK to RIO_DCLK conversion
-- ----------------------------------------------------------------------------

TX_RECLOCK : process(reset_i,GMII_TX_CLK)
begin
   if (GMII_TX_CLK'event and GMII_TX_CLK = '1') then
      rio_txdata <= reg_txdata;
   end if;
end process;

RX_ALIGN : process(reset_i,REFCLK)
begin
   if (reset_i = '1') then
      rxdata       <= (others => '0');
      rxdisperr    <= '0';
      rxnotintable <= '0';
      rxcharisk    <= '0';
   elsif (REFCLK'event and REFCLK = '1') then
      rxdata       <= rio_rxdata;
      rxdisperr    <= rio_rxdisperr;
      rxnotintable <= rio_rxnotintable;
      rxcharisk    <= rio_rxcharisk;
   end if;
end process;

-- For simulation purposes only
rxdata_dly       <= rxdata       --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxdisperr_dly    <= rxdisperr    --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxnotintable_dly <= rxnotintable --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;
rxcharisk_dly    <= rxcharisk    --pragma translate_off
                    after 1 ns   --pragma translate_on
                    ;


-- ----------------------------------------------------------------------------
-- Auto-negotiation -----------------------------------------------------------
-- ----------------------------------------------------------------------------

STORE_RX_CFG: process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (an_valid_rise = '1') then 
         rx_config_reg <= (others => '0');
      elsif (an_valid = '1') then
         if (rx_cfg_d0 = '1') then
            rx_config_reg(7 downto 0) <= reg_rxdata;
         end if;
         if (rx_cfg_d1 = '1') then
            rx_config_reg(15 downto 8) <= reg_rxdata;
         end if;
      end if;
      
      reg_an_valid <= an_valid;

      if (rx_config_reg = X"0000") then
         rx_cfgr_zero  <= '1';
      else
         rx_cfgr_zero  <= '0';
      end if;
   end if;
end process;

an_valid      <= '1' when (rx_cfg_det = '1') and (rx_cfg_cntr = "11")
                 else '0';
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
         if (an_start = '1') then
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

TX_CFG_REG : process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (tx_cfgr_wen = '1') then
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
         if ((tx_cfg = '1') and (txdata_pcs(8) = '1')) then -- Sychronize K28p5 with PCS
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
         txdata_cfg <= "00" & tx_config_reg(7 downto 0);
         cfg_data_next_state <= DATA0_1;
         
      when DATA0_1 =>
         cfgtx_state_d <= X"6";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg(15 downto 8);
         cfg_data_next_state <= C1;

      when DATA1 =>
         cfgtx_state_d <= X"7";
         tx_sel_cfg <= '1';
         txdata_cfg <= "00" & tx_config_reg(7 downto 0);
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

AN_FSM_SEQ : process(REFCLK, reset_i)
begin
   if (reset_i = '1') then
      an_state       <= IDLE;
      cfg_data_state <= IDLE;
   elsif (REFCLK'event and REFCLK = '1') then
      an_state       <= an_next_state;
      cfg_data_state <= cfg_data_next_state;
   end if;
end process;

end behavioral;
