-- rio_emac.vhd: RocketIO to EMAC SGMII interface converter
-- Copyright (C) 2009 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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

entity rio_emac is
   generic (
      EMAC_REGS_EN   : boolean := FALSE;
      RIO_REGS_EN    : boolean := FALSE
   );
   port (
      -- Reference clock signal - 125 MHz
      REFCLK         : in  std_logic;
      -- Global reset
      RESET          : in  std_logic;

      -- EMAC PHY interface
      EMAC_RX_DATA         : out  std_logic_vector(7 downto 0);
      EMAC_RX_CHARISCOMMA  : out  std_logic;
      EMAC_RX_CHARISK      : out  std_logic;
      EMAC_RX_DISPERR      : out  std_logic;
      EMAC_RX_NOTINTABLE   : out  std_logic;
      EMAC_RX_RUNDISP      : out  std_logic;

      EMAC_RX_CLKCORCNT    : out  std_logic_vector(2 downto 0);

      EMAC_TX_DATA         : in std_logic_vector(7 downto 0);
      EMAC_TX_CHARISK      : in std_logic;
      EMAC_TX_CHARDISPMODE : in std_logic;
      EMAC_TX_CHARDISPVAL  : in std_logic;

      -- GTP interface
      RIO_RX_DATA         : in  std_logic_vector(7 downto 0);
      RIO_RX_CHARISCOMMA  : in  std_logic;
      RIO_RX_CHARISK      : in  std_logic;
      RIO_RX_DISPERR      : in  std_logic;
      RIO_RX_NOTINTABLE   : in  std_logic;
      RIO_RX_RUNDISP      : in  std_logic;

      RIO_RX_CLKCORCNT    : in  std_logic_vector(2 downto 0);

      RIO_TX_DATA         : out std_logic_vector(7 downto 0);
      RIO_TX_CHARISK      : out std_logic;
      RIO_TX_CHARDISPMODE : out std_logic;
      RIO_TX_CHARDISPVAL  : out std_logic
    );
end rio_emac;

architecture behavioral of rio_emac is

   -- -------------------------------------------------------------------------
   --                          Constant Declaration
   -- -------------------------------------------------------------------------
   constant K28p5 : std_logic_vector(7 downto 0) := X"BC"; -- OK

   -- -------------------------------------------------------------------------
   --                          Type Declarations
   -- -------------------------------------------------------------------------
   
   type T_AN_STATE is (IDLE, AN_CFG_WAIT, CFG_DATA, CFG_ACK);
   type T_CFG_DATA_STATE is (IDLE, C0, C0_1, C1, C1_1, DATA0, DATA0_1, DATA1, DATA1_1);
   type T_RX_MON_STATE is (IDLE, OSET, CFG_D0, CFG_D1);
   
   -- -------------------------------------------------------------------------
   --                          Signal Declarations
   -- -------------------------------------------------------------------------

   ----- Reset and other auxiliary signals -----
   signal reset_i                   : std_logic;
   signal rst_cntr                  : std_logic_vector(4 downto 0);
   signal cycle                     : std_logic := '0';


   ----- RX direction -----
   -- RIO input registers
   signal reg_rio_rx_data           : std_logic_vector(7 downto 0);
   signal reg_rio_rx_chariscomma    : std_logic;
   signal reg_rio_rx_charisk        : std_logic;
   signal reg_rio_rx_disperr        : std_logic;
   signal reg_rio_rx_notintable     : std_logic;
   signal reg_rio_rx_rundisp        : std_logic;
   signal reg_rio_rx_clkcorcnt      : std_logic_vector(2 downto 0);
   
   -- EMAC output registers
   signal reg_emac_rx_data          : std_logic_vector(7 downto 0);
   signal reg_emac_rx_chariscomma   : std_logic;
   signal reg_emac_rx_charisk       : std_logic;
   signal reg_emac_rx_disperr       : std_logic;
   signal reg_emac_rx_notintable    : std_logic;
   signal reg_emac_rx_rundisp       : std_logic;
   signal reg_emac_rx_clkcorcnt     : std_logic_vector(2 downto 0);
   
   -- Signals interconnecting input and output registers
   signal rx_data                   : std_logic_vector(7 downto 0);
   signal rx_chariscomma            : std_logic;
   signal rx_charisk                : std_logic;
   signal rx_disperr                : std_logic;
   signal rx_notintable             : std_logic;
   signal rx_rundisp                : std_logic;
   signal rx_clkcorcnt              : std_logic_vector(2 downto 0);


   ----- TX direction -----
   -- RIO output registers
   signal reg_rio_tx_data           : std_logic_vector(9 downto 0);
   signal reg_rio_tx_chardispmode   : std_logic;
   signal reg_rio_tx_chardispval    : std_logic;

   -- EMAC input registers
   signal reg_emac_tx_data          : std_logic_vector(7 downto 0);
   signal reg_emac_tx_charisk       : std_logic;
   signal reg_emac_tx_chardispmode  : std_logic;
   signal reg_emac_tx_chardispval   : std_logic;

   -- EMAC TX data (10th bit is 0, 9th bit is value of chrisk signal)
   signal tx_data_emac              : std_logic_vector(9 downto 0);
   
   -- Configuration TX data (10th bit is 0, 9th bit is value of chrisk signal)
   signal tx_data_cfg               : std_logic_vector(9 downto 0);
   
   -- EMAC or CFG data in TX (10th bit is 0, 9th bit is value of chrisk signal)
   signal tx_data                   : std_logic_vector(9 downto 0);
   
   -- Signals interconnecting input and output registers
   signal tx_chardispmode           : std_logic;
   signal tx_chardispval            : std_logic;


   ----- RX monitoring signals -----
   -- Type of codegroup in RX
   signal rx_char_val               : std_logic;
   signal rx_kchar_val              : std_logic;
   signal rx_dchar_val              : std_logic;

   -- RX line flags
   signal rx_idle                   : std_logic;
   signal rx_cfg_det                : std_logic;

   -- RX monitor FSM states
   signal rx_mon_state              : t_rx_mon_state;
   signal rx_mon_next_state         : t_rx_mon_state;

   -- RX line status indicators
   signal rx_set_err                : std_logic;
   signal rx_set_idle               : std_logic;
   signal rx_clr_cfg                : std_logic;


   ----- Auto-negotiation -----
   -- RX configuration-related signals
   signal rx_cfg_cntr               : std_logic_vector(1 downto 0) := "00";
   signal rx_cfg_d0                 : std_logic := '0';
   signal rx_cfg_d1                 : std_logic := '0';
   signal rx_config_reg             : std_logic_vector(15 downto 0):= (others => '0');
   signal rx_cfgr_zero              : std_logic;

   -- TX configuration-related signals
   signal tx_cfg                    : std_logic;
   signal tx_sel_cfg                : std_logic;
   signal tx_config_reg             : std_logic_vector(15 downto 0);
   signal tx_config_i               : std_logic_vector(15 downto 0);
   signal tx_cfgr_wen               : std_logic;
   
   -- Auto-Negotiation auxiliary signals
   signal an_start                  : std_logic;
   signal an_valid                  : std_logic;
   signal an_valid_rise             : std_logic;
   signal reg_an_valid              : std_logic;
   
   -- Auto-Negotiation FSM states
   signal an_state                  : t_an_state;
   signal an_next_state             : t_an_state;
   signal cfg_data_state            : t_cfg_data_state;
   signal cfg_data_next_state       : t_cfg_data_state;

   -- FSMs state debug info
   signal an_state_d                : std_logic_vector(3 downto 0);
   signal cfgtx_state_d             : std_logic_vector(3 downto 0);
   
   
begin

-------------------------------------------------------------------------------
-- Main code
-------------------------------------------------------------------------------

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
end process POWERUP_RESET;

CYCLE_REG : process (reset_i, REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      cycle <= not cycle;
   end if;
end process CYCLE_REG;

-------------------------------------------------------------------------------
-- Generate RIO side registers
-------------------------------------------------------------------------------

GENARATE_RIO_REGS : if (RIO_REGS_EN = TRUE) generate

   ----- RIO input registers -------------------------------------------------- 

   RIO_IN_REGS : process(REFCLK)
   begin
      if (REFCLK'event and REFCLK = '1') then
         if (reset_i = '1') then
            reg_rio_rx_data         <= (others => '0');
            reg_rio_rx_chariscomma  <= '0';
            reg_rio_rx_charisk      <= '0';
            reg_rio_rx_disperr      <= '0';
            reg_rio_rx_notintable   <= '0';
            reg_rio_rx_rundisp      <= '0';
            reg_rio_rx_clkcorcnt    <= "000";
         else
            reg_rio_rx_data         <= RIO_RX_DATA;
            reg_rio_rx_chariscomma  <= RIO_RX_CHARISCOMMA;
            reg_rio_rx_charisk      <= RIO_RX_CHARISK;
            reg_rio_rx_disperr      <= RIO_RX_DISPERR;
            reg_rio_rx_notintable   <= RIO_RX_NOTINTABLE;
            reg_rio_rx_rundisp      <= RIO_RX_RUNDISP;
            reg_rio_rx_clkcorcnt    <= RIO_RX_CLKCORCNT;
        end if;
      end if;
   end process RIO_IN_REGS;

   ----- RIO output registers -------------------------------------------------

   RIO_OUT_REGS : process(REFCLK)
   begin
      if (REFCLK'event and REFCLK = '1') then
         if (reset_i = '1') then
            -- IDLE pattern
            if (cycle = '0') then
               reg_rio_tx_data  <= "01" & K28p5;
            else
               reg_rio_tx_data  <= "00" & X"50";
            end if;
            reg_rio_tx_chardispmode <= '0';
            reg_rio_tx_chardispval  <= '0';
         else
            reg_rio_tx_data         <= tx_data;
            reg_rio_tx_chardispmode <= tx_chardispmode;
            reg_rio_tx_chardispval  <= tx_chardispval;
         end if;
      end if;
   end process RIO_OUT_REGS;

end generate; 

-------------------------------------------------------------------------------
-- Direct input/output on RIO side
-------------------------------------------------------------------------------

NOT_GENARATE_RIO_REGS : if (RIO_REGS_EN = FALSE) generate

   ----- Input signals --------------------------------------------------------
   
   reg_rio_rx_data         <= RIO_RX_DATA;
   reg_rio_rx_chariscomma  <= RIO_RX_CHARISCOMMA;
   reg_rio_rx_charisk      <= RIO_RX_CHARISK;
   reg_rio_rx_disperr      <= RIO_RX_DISPERR;
   reg_rio_rx_notintable   <= RIO_RX_NOTINTABLE;
   reg_rio_rx_rundisp      <= RIO_RX_RUNDISP;
   reg_rio_rx_clkcorcnt    <= RIO_RX_CLKCORCNT;

   ----- Output signals --------------------------------------------------------
   
   reg_rio_tx_data         <= tx_data;
   reg_rio_tx_chardispmode <= tx_chardispmode;
   reg_rio_tx_chardispval  <= tx_chardispval;

end generate; 

-------------------------------------------------------------------------------
-- Generate EMAC side registers
-------------------------------------------------------------------------------

GENARATE_EMAC_REGS : if (EMAC_REGS_EN = TRUE) generate

   ----- EMAC input registers ------------------------------------------------- 

   EMAC_IN_REGS : process(REFCLK)
   begin
      if (REFCLK'event and REFCLK = '1') then
         if (reset_i = '1') then
            reg_emac_tx_data           <= (others => '0');
            reg_emac_tx_charisk        <= '0';
            reg_emac_tx_chardispmode   <= '0';
            reg_emac_tx_chardispval    <= '0';
         else
            reg_emac_tx_data           <= EMAC_TX_DATA;
            reg_emac_tx_charisk        <= EMAC_TX_CHARISK;
            reg_emac_tx_chardispmode   <= EMAC_TX_CHARDISPMODE;
            reg_emac_tx_chardispval    <= EMAC_TX_CHARDISPVAL;
         end if;
      end if;
   end process EMAC_IN_REGS;

   ----- EMAC output registers ------------------------------------------------

   EMAC_OUT_REGS : process(REFCLK)
   begin
      if (REFCLK'event and REFCLK = '1') then
         if (reset_i = '1') then
            reg_emac_rx_data        <= (others => '0');
            reg_emac_rx_chariscomma <= '0';
            reg_emac_rx_charisk     <= '0';
            reg_emac_rx_disperr     <= '0';
            reg_emac_rx_notintable  <= '0';
            reg_emac_rx_rundisp     <= '0';
            reg_emac_rx_clkcorcnt   <= "000";
         else
            reg_emac_rx_data        <= rx_data;
            reg_emac_rx_chariscomma <= rx_chariscomma;
            reg_emac_rx_charisk     <= rx_charisk;
            reg_emac_rx_disperr     <= rx_disperr;
            reg_emac_rx_notintable  <= rx_notintable;
            reg_emac_rx_rundisp     <= rx_rundisp;
            reg_emac_rx_clkcorcnt   <= rx_clkcorcnt;
         end if;
      end if;
   end process EMAC_OUT_REGS;

end generate; 

-------------------------------------------------------------------------------
-- Direct input/output on EMAC side
-------------------------------------------------------------------------------

NOT_GENARATE_EMAC_REGS : if (EMAC_REGS_EN = FALSE) generate

   ----- Input signals --------------------------------------------------------
   
   reg_emac_tx_data           <= EMAC_TX_DATA;
   reg_emac_tx_charisk        <= EMAC_TX_CHARISK;
   reg_emac_tx_chardispmode   <= EMAC_TX_CHARDISPMODE;
   reg_emac_tx_chardispval    <= EMAC_TX_CHARDISPVAL;
  
   ----- Output signals --------------------------------------------------------
 
   reg_emac_rx_data           <= rx_data;
   reg_emac_rx_chariscomma    <= rx_chariscomma;
   reg_emac_rx_charisk        <= rx_charisk;
   reg_emac_rx_disperr        <= rx_disperr;
   reg_emac_rx_notintable     <= rx_notintable;
   reg_emac_rx_rundisp        <= rx_rundisp;
   reg_emac_rx_clkcorcnt      <= rx_clkcorcnt;

end generate; 

-------------------------------------------------------------------------------
-- Assign values to output signals on RIO side of the component
-------------------------------------------------------------------------------

RIO_TX_DATA            <= reg_rio_tx_data(7 downto 0);
RIO_TX_CHARISK         <= reg_rio_tx_data(8);
RIO_TX_CHARDISPMODE    <= reg_rio_tx_chardispmode;
RIO_TX_CHARDISPVAL     <= reg_rio_tx_chardispval;

-------------------------------------------------------------------------------
-- Assign values to output signals on EMAC side of the component
-------------------------------------------------------------------------------

EMAC_RX_DATA         <= reg_emac_rx_data;
EMAC_RX_CHARISCOMMA  <= reg_emac_rx_chariscomma;
EMAC_RX_CHARISK      <= reg_emac_rx_charisk;
EMAC_RX_DISPERR      <= reg_emac_rx_disperr;
EMAC_RX_NOTINTABLE   <= reg_emac_rx_notintable;
EMAC_RX_RUNDISP      <= reg_emac_rx_rundisp;
EMAC_RX_CLKCORCNT    <= reg_emac_rx_clkcorcnt;

-------------------------------------------------------------------------------
-- TX datapath
-------------------------------------------------------------------------------

tx_data_emac      <= '0' & reg_emac_tx_charisk & reg_emac_tx_data;

tx_data           <= tx_data_cfg when tx_sel_cfg = '1' else
                     tx_data_emac;
tx_chardispmode   <= '0' when tx_sel_cfg = '1' else
		     reg_emac_tx_chardispmode;
tx_chardispval    <= '0' when tx_sel_cfg = '1' else 
		     reg_emac_tx_chardispval;

-------------------------------------------------------------------------------
-- RX datapath
-------------------------------------------------------------------------------

rx_data        <= K28p5 when ((an_valid = '1') and (cycle = '0')) else
                  X"50" when ((an_valid = '1') and (cycle = '1')) else
                  reg_rio_rx_data;
rx_chariscomma <= '1' when ((an_valid = '1') and (cycle = '0')) else
                  '0' when ((an_valid = '1') and (cycle = '1')) else
		  reg_rio_rx_chariscomma;
rx_charisk     <= '1' when ((an_valid = '1') and (cycle = '0')) else
                  '0' when ((an_valid = '1') and (cycle = '1')) else
		  reg_rio_rx_charisk;
rx_disperr     <= reg_rio_rx_disperr;
rx_notintable  <= reg_rio_rx_notintable;
rx_rundisp     <= reg_rio_rx_rundisp;
rx_clkcorcnt   <= reg_rio_rx_clkcorcnt;

-------------------------------------------------------------------------------
-- RX monitoring
-------------------------------------------------------------------------------

rx_char_val  <= (not reg_rio_rx_notintable) and (not reg_rio_rx_disperr);
rx_kchar_val <= reg_rio_rx_charisk and rx_char_val;
rx_dchar_val <= (not reg_rio_rx_charisk) and rx_char_val;

rx_idle <= '1' when ((rx_kchar_val = '1') and (reg_rio_rx_data = K28p5))
           else '0';


-- FSM monitors RX line status
RX_MONITOR : process(rx_mon_state, rx_char_val, rx_dchar_val, rx_idle, reg_rio_rx_data)
begin
   rx_cfg_d0   <= '0';
   rx_cfg_d1   <= '0';
   rx_set_err  <= '0';
   rx_set_idle <= '0';
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
            if ((reg_rio_rx_data = X"42") or (reg_rio_rx_data = X"B5")) then
               rx_mon_next_state <= CFG_D0;  -- Configuration
            elsif ((reg_rio_rx_data = X"C5") or (reg_rio_rx_data = X"50")) then
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
end process RX_MONITOR;


RX_MON_SEQ : process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (reset_i = '1') then
         rx_mon_state   <= IDLE;
      else
         rx_mon_state   <= rx_mon_next_state;
      end if;
   end if;
end process RX_MON_SEQ;


RX_LINE_FLAGS : process(REFCLK)
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
   end if;
end process RX_LINE_FLAGS;

-- ----------------------------------------------------------------------------
-- Auto-negotiation
-- ----------------------------------------------------------------------------

an_valid      <= '1' when (rx_cfg_det = '1') and (rx_cfg_cntr = "11")
                 else '0';
an_valid_rise <= an_valid and (not reg_an_valid);
an_start      <= an_valid and rx_cfgr_zero;


STORE_RX_CFG : process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (an_valid_rise = '1') then 
         rx_config_reg <= (others => '0');
      elsif (an_valid = '1') then
         if (rx_cfg_d0 = '1') then
            rx_config_reg(7 downto 0) <= reg_rio_rx_data;
         end if;
         if (rx_cfg_d1 = '1') then
            rx_config_reg(15 downto 8) <= reg_rio_rx_data;
         end if;
      end if;
      
      reg_an_valid <= an_valid;

      if (rx_config_reg = X"0000") then
         rx_cfgr_zero  <= '1';
      else
         rx_cfgr_zero  <= '0';
      end if;
   end if;
end process STORE_RX_CFG;


AN_FSM : process(an_state, an_start, an_valid, rx_cfgr_zero, rx_config_reg)
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
end process AN_FSM;

TX_CFG_REG : process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (tx_cfgr_wen = '1') then
         tx_config_reg <= tx_config_i;
      end if;
   end if;
end process TX_CFG_REG;

-- Generate /C/ (configuration) ordered set ----------------------------------
CFG_DATA_FSM : process(cfg_data_state, tx_cfg, tx_data_emac, tx_config_reg)
begin
   cfgtx_state_d <= X"0";
   tx_sel_cfg    <= '0';
   tx_cfgr_wen   <= '0';
   
   case cfg_data_state is

      -- Idle or first /C1/ ordered set
      when IDLE => 
         cfgtx_state_d <= X"0";
         tx_data_cfg <= "01" & K28p5;
         if ((tx_cfg = '1') and (tx_data_emac(8) = '1')) then -- Sychronize K28p5 with PCS
            tx_sel_cfg  <= '1';
            tx_cfgr_wen <= '1';
            cfg_data_next_state <= C0_1;
         else
            cfg_data_next_state <= IDLE;
         end if;
         
      -- /C1/ ordered set
      when C0 =>
         cfgtx_state_d <= X"1";
         tx_data_cfg <= "01" & K28p5;
         tx_sel_cfg  <= '1';
         tx_cfgr_wen <= '1';
         cfg_data_next_state <= C0_1;
         
      when C0_1 =>
         cfgtx_state_d <= X"2";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & X"B5"; -- /C1/ ordered set
         cfg_data_next_state <= DATA0;

      -- /C2/ ordered set
      when C1 =>
         cfgtx_state_d <= X"3";
         tx_data_cfg <= "01" & K28p5;
         tx_sel_cfg <= '1';
         cfg_data_next_state <= C1_1;
         
      when C1_1 =>
         cfgtx_state_d <= X"4";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & X"42";
         cfg_data_next_state <= DATA1;

      -- tx_data_reg
      when DATA0 =>
         cfgtx_state_d <= X"5";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & tx_config_reg(7 downto 0);
         cfg_data_next_state <= DATA0_1;
         
      when DATA0_1 =>
         cfgtx_state_d <= X"6";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & tx_config_reg(15 downto 8);
         cfg_data_next_state <= C1;

      when DATA1 =>
         cfgtx_state_d <= X"7";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & tx_config_reg(7 downto 0);
         cfg_data_next_state <= DATA1_1;
         
      when DATA1_1 =>
         cfgtx_state_d <= X"8";
         tx_sel_cfg <= '1';
         tx_data_cfg <= "00" & tx_config_reg(15 downto 8);
         if (tx_cfg = '1') then
            cfg_data_next_state <= C0;
         else
            cfg_data_next_state <= IDLE;
         end if;

   end case;
end process CFG_DATA_FSM;


AN_FSM_SEQ : process(REFCLK)
begin
   if (REFCLK'event and REFCLK = '1') then
      if (reset_i = '1') then
         an_state       <= IDLE;
         cfg_data_state <= IDLE;
      else
         an_state       <= an_next_state;
         cfg_data_state <= cfg_data_next_state;
      end if;
   end if;
end process AN_FSM_SEQ;


end behavioral;
