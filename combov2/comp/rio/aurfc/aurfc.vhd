
-- aurfc.vhd: Architecture of aurfc entity 
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
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of aurfc is

component fc_transmitter is
   generic (
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 3;
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- User LocalLink TX interface
      TXU_D             : in std_logic_vector(0 to DATA_WIDTH-1);
      TXU_REM           : in std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      TXU_SRC_RDY_N     : in std_logic;
      TXU_SOP_N         : in std_logic;
      TXU_EOP_N         : in std_logic;
      TXU_DST_RDY_N     : out std_logic;

      -- Aurora LocalLink TX interface
      TXA_D             : out std_logic_vector(0 to DATA_WIDTH-1);
      TXA_REM           : out std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      TXA_SRC_RDY_N     : out std_logic;
      TXA_SOP_N         : out std_logic;
      TXA_EOP_N         : out std_logic;
      TXA_DST_RDY_N     : in std_logic;

      -- Aurora Status Interface
      CHANNEL_UP       : in std_logic;

      -- Status Interface
      TX_STATUS         : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0) 
   );
end component;

component fc_receiver is
   generic (
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 3;
      DATA_WIDTH        : integer;
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";
      DISCARD_BAD_PACKETS : boolean := false
   );
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- User LocalLink RX interface
      RXU_D             : out std_logic_vector(0 to DATA_WIDTH-1);
      RXU_REM           : out std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      RXU_SRC_RDY_N     : out std_logic;
      RXU_SOP_N         : out std_logic;
      RXU_EOP_N         : out std_logic;
      RXU_DST_RDY_N     : in std_logic;

      -- Aurora LocalLink RX interface
      RXA_D             : in std_logic_vector(0 to DATA_WIDTH-1);
      RXA_REM           : in std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      RXA_SRC_RDY_N     : in std_logic;
      RXA_SOP_N         : in std_logic;
      RXA_EOP_N         : in std_logic;

      -- Aurora Native Flow Control Interface
      NFC_REQ_N        : out std_logic;
      NFC_NB           : out std_logic_vector(0 to 3);
      NFC_ACK_N        : in std_logic;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : in std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : in std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                         -- asserted for a single clock).
      FRAME_ERROR    : in std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                         -- and is asserted for a single clock.
      -- Status Interface
      RX_STATUS         : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);

      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);     
      D_CNT_XON   : out std_logic_vector(31 downto 0);
      D_CNT_XOFF  : out std_logic_vector(31 downto 0);
      D_FULL      : out std_logic_vector(15 downto 0)
   );
end component;

component rio_aurora_module is
    generic (                    
         LANES             : integer;     -- Number of lanes 
         DATA_PATHS        : integer      -- Number of data paths
    );
    port (

    -- LocalLink TX Interface

            TX_D             : in std_logic_vector(0 to (DATA_PATHS*8)-1);
            TX_REM           : in std_logic_vector(0 to log2(DATA_PATHS)-1);
            TX_SRC_RDY_N     : in std_logic;
            TX_SOF_N         : in std_logic;
            TX_EOF_N         : in std_logic;
            TX_DST_RDY_N     : out std_logic;

    -- LocalLink RX Interface

            RX_D             : out std_logic_vector(0 to (DATA_PATHS*8)-1);
            RX_REM           : out std_logic_vector(0 to log2(DATA_PATHS)-1);
            RX_SRC_RDY_N     : out std_logic;
            RX_SOF_N         : out std_logic;
            RX_EOF_N         : out std_logic;

    -- Native Flow Control Interface

            NFC_REQ_N        : in std_logic;
            NFC_NB           : in std_logic_vector(0 to 3);
            NFC_ACK_N        : out std_logic;

    -- User Flow Control TX Interface

            UFC_TX_REQ_N     : in std_logic;
            UFC_TX_MS        : in std_logic_vector(0 to 2);
            UFC_TX_ACK_N     : out std_logic;

    -- User Flow Control RX Inteface

            UFC_RX_DATA      : out std_logic_vector(0 to (DATA_PATHS*8)-1);
            UFC_RX_REM       : out std_logic_vector(0 to log2(DATA_PATHS)-1);
            UFC_RX_SRC_RDY_N : out std_logic;
            UFC_RX_SOF_N     : out std_logic;
            UFC_RX_EOF_N     : out std_logic;

    -- MGT Serial I/O

            RXN            : in  std_logic_vector(0 to LANES-1);
            RXP            : in  std_logic_vector(0 to LANES-1);

            TXN            : out std_logic_vector(0 to LANES-1);
            TXP            : out std_logic_vector(0 to LANES-1);

    -- MGT Reference Clock Interface

            TOP_REF_CLK     : in std_logic;

    -- Error Detection Interface

            HARD_ERROR       : out std_logic;
            SOFT_ERROR       : out std_logic;
            FRAME_ERROR      : out std_logic;

    -- Status

            CHANNEL_UP       : out std_logic;
            LANE_UP          : out std_logic_vector(0 to LANES-1);

    -- Clock Compensation Control Interface

            WARN_CC          : in std_logic;
            DO_CC            : in std_logic;

    -- System Interface

            DCM_NOT_LOCKED   : in std_logic;
            USER_CLK         : in std_logic;
            USER_CLK_N_2X    : in std_logic;
            RESET            : in std_logic;
            POWER_DOWN       : in std_logic;
            LOOPBACK         : in std_logic_vector(1 downto 0)

         );

end component;

component SOF_EOF_generator is
   generic (
      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true
   );   
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      CLK            : in std_logic;      -- Standart clock input
      EN             : in std_logic;      -- Enable input

      -- RX SOP/EOP signals
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;

      -- Generated EX SOF/EOF signals
      RX_SOF_N       : out std_logic;
      RX_EOF_N       : out std_logic
   );
end component;

-- common signals
signal gnd     : std_logic;
signal pwr     : std_logic;
signal aur_clk : std_logic;

signal txa_d    :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal txa_rem     :  std_logic_vector(0 to log2(DATA_PATHS)-1);
signal txa_src_rdy_n     :  std_logic;
signal txa_sop_n      :  std_logic;
signal txa_eop_n      :  std_logic;
signal txa_dst_rdy_n     :  std_logic;
signal rxa_d    :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal rxa_rem     :  std_logic_vector(0 to log2(DATA_PATHS)-1);
signal rxa_src_rdy_n     :  std_logic;
signal rxa_sop_n      :  std_logic;
signal rxa_eop_n      :  std_logic;
signal rxu_src_rdy_n     :  std_logic;
signal rxu_sop_n      :  std_logic;
signal rxu_eop_n      :  std_logic;

signal tx_d_rev      :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal tx_d_i        :  std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal tx_rem_rev    :  std_logic_vector(0 to log2(DATA_PATHS)-1);
signal rx_d_rev      :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal rx_d_i        :  std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal rx_rem_rev    :  std_logic_vector(0 to log2(DATA_PATHS)-1);

signal nfc_req_n     :  std_logic;
signal nfc_nb     :  std_logic_vector(0 to 3);
signal nfc_ack_n     :  std_logic;

signal output_valid : std_logic;

signal hard_error_i : std_logic;
signal soft_error_i : std_logic;
signal frame_error_i : std_logic;
signal channel_up_i : std_logic;
signal reg_chnl_up  : std_logic;
signal warn_cc : std_logic;
signal power_down : std_logic;

-- Clock compensation logic signals
signal cnt_cc_gap : std_logic_vector(12 downto 0);
signal cnt_cc_gap_ovf : std_logic;
signal cnt_cc_gap_warn: std_logic;
signal cnt_cc_cycles : std_logic_vector(2 downto 0);
signal cnt_cc_cycles_ovf : std_logic;
signal reg_do_cc : std_logic;
signal reg_do_cc_dly : std_logic;
signal reg_warn_cc : std_logic;
signal reg_warn_cc_dly  : std_logic;
signal chnl_initialized : std_logic;

begin

gnd <= '0';
pwr <= '1';

twobyte_aurora_inst_gen: if (DATA_PATHS/LANES = 2) generate
   aur_clk <= USRCLK;
end generate;

non_twobyte_aurora_inst_gen: if (DATA_PATHS/LANES = 4) generate
   aur_clk <= USRCLK2;
end generate;

transmitter_u: fc_transmitter
   generic map(
      TX_FIFO_ITEMS     => TX_FIFO_ITEMS,
      TX_STATUS_WIDTH   => TX_STATUS_WIDTH,
      DATA_WIDTH        => (DATA_PATHS*8)
   )
   port map(
      -- Common Input
      USRCLK2  => aur_clk,
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- User LocalLink TX interface
      TXU_D             => tx_d_rev,
      TXU_REM           => tx_rem_rev,
      TXU_SRC_RDY_N     => TX_SRC_RDY_N,
      TXU_SOP_N         => TX_SOP_N,
      TXU_EOP_N         => TX_EOP_N,
      TXU_DST_RDY_N     => TX_DST_RDY_N,

      -- Aurora LocalLink TX interface
      TXA_D             => txa_d,
      TXA_REM           => txa_rem,
      TXA_SRC_RDY_N     => txa_src_rdy_n,
      TXA_SOP_N         => txa_sop_n,
      TXA_EOP_N         => txa_eop_n,
      TXA_DST_RDY_N     => txa_dst_rdy_n,

      -- Aurora Status Interface
      CHANNEL_UP       => channel_up_i,

      -- Status Interface
      TX_STATUS         => TX_STATUS

   );

receiver_u: fc_receiver
   generic map(
      RX_FIFO_ITEMS     => RX_FIFO_ITEMS,
      RX_STATUS_WIDTH   => RX_STATUS_WIDTH,
      DATA_WIDTH        => (DATA_PATHS*8),
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT,
      DISCARD_BAD_PACKETS => false
--      DISCARD_BAD_PACKETS => DISCARD_BAD_PACKETS
   )
   port map(
      -- Common Input
      USRCLK2  => aur_clk,
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- User LocalLink RX interface
      RXU_D             => rx_d_rev,
      RXU_REM           => rx_rem_rev,
      RXU_SRC_RDY_N     => rxu_src_rdy_n,
      RXU_SOP_N         => rxu_sop_n,
      RXU_EOP_N         => rxu_eop_n,
      RXU_DST_RDY_N     => RX_DST_RDY_N,

      -- Aurora LocalLink RX interface
      RXA_D             => rxa_d,
      RXA_REM           => rxa_rem,
      RXA_SRC_RDY_N     => rxa_src_rdy_n,
      RXA_SOP_N         => rxa_sop_n,
      RXA_EOP_N         => rxa_eop_n,

      -- Aurora Native Flow Control Interface
      NFC_REQ_N        => nfc_req_n,
      NFC_NB           => nfc_nb,
      NFC_ACK_N        => nfc_ack_n,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => hard_error_i,
      SOFT_ERROR     => soft_error_i,
      FRAME_ERROR    => frame_error_i,

      -- Status Interface
      RX_STATUS         => RX_STATUS,
      
      -- Debug
      D_STATE        => D_STATE,
      D_CNT_XON   => D_CNT_XON,
      D_CNT_XOFF  => D_CNT_XOFF,
      D_FULL      => D_RX_FULL
   );

   -- Remap 'to' vector <-> 'downto' vector
--   to_downto_remap_gen: for i in 0 to (DATA_PATHS*8)-1 generate
--      tx_d_rev(i) <= tx_d_i((DATA_PATHS*8)-i-1);
--      rx_d_i(i) <= rx_d_rev((DATA_PATHS*8)-i-1);
--   end generate;
   tx_d_rev <= tx_d_i;
   rx_d_i <= rx_d_rev;

--   to_downto_remap_gen2: for i in 0 to log2(DATA_PATHS)-1 generate
--      tx_rem_rev(i) <= TX_REM(log2(DATA_PATHS)-i-1);
--      RX_REM(i) <= rx_rem_rev(log2(DATA_PATHS)-i-1);
--   end generate;
   tx_rem_rev <= TX_REM;
   RX_REM <= rx_rem_rev;

   -- Remap Big Endian <-> Little Endian
   to_little_endian_gen: for i in 0 to (DATA_PATHS)-1 generate
      tx_d_i(((i+1)*8)-1 downto i*8) <= TX_D((((DATA_PATHS)-i)*8)-1 downto ((DATA_PATHS)-i-1)*8);
      RX_D(((i+1)*8)-1 downto i*8) <= rx_d_i((((DATA_PATHS)-i)*8)-1 downto ((DATA_PATHS)-i-1)*8);
   end generate;

   RX_SRC_RDY_N <= rxu_src_rdy_n;
   RX_SOP_N <= rxu_sop_n;
   RX_EOP_N <= rxu_eop_n;


rio_aurora_module_u: rio_aurora_module
    generic map(
            LANES       => LANES,
            DATA_PATHS  => DATA_PATHS
    )
    port map(
            -- LocalLink TX Interface
            TX_D             => txa_d,
            TX_REM           => txa_rem,
            TX_SRC_RDY_N     => txa_src_rdy_n,
            TX_SOF_N         => txa_sop_n,
            TX_EOF_N         => txa_eop_n,
            TX_DST_RDY_N     => txa_dst_rdy_n,

            -- LocalLink RX Interface
            RX_D             => rxa_d,
            RX_REM           => rxa_rem,
            RX_SRC_RDY_N     => rxa_src_rdy_n,
            RX_SOF_N         => rxa_sop_n,
            RX_EOF_N         => rxa_eop_n,

            -- Native Flow Control Interface
            NFC_REQ_N        => nfc_req_n,
            NFC_NB           => nfc_nb,
            NFC_ACK_N        => nfc_ack_n,

            -- User Flow Control TX Interface

            UFC_TX_REQ_N     => '1',
            UFC_TX_MS        => "000",
            UFC_TX_ACK_N     => open,

            -- User Flow Control RX Inteface

            UFC_RX_DATA      => open,
            UFC_RX_REM       => open,
            UFC_RX_SRC_RDY_N => open,
            UFC_RX_SOF_N     => open,
            UFC_RX_EOF_N     => open,

            -- MGT Serial I/O
            RXP              => RXP,
            RXN              => RXN,
            TXP              => TXP,
            TXN              => TXN,

            -- MGT Reference Clock Interface
            TOP_REF_CLK      => REFCLK,

            -- Error Detection Interface
            HARD_ERROR       => hard_error_i,
            SOFT_ERROR       => soft_error_i,
            FRAME_ERROR      => frame_error_i,

            -- Status
            CHANNEL_UP       => channel_up_i,
            LANE_UP          => open,

            -- Clock Compensation Control Interface
            WARN_CC          => reg_warn_cc_dly,
            DO_CC            => reg_do_cc_dly,

            -- System Interface
            DCM_NOT_LOCKED   => RESET,
            USER_CLK         => aur_clk,
            USER_CLK_N_2X    => USRCLK,
            RESET            => RESET,
            POWER_DOWN       => power_down,
            LOOPBACK         => LOOPBACK
         );
HARD_ERROR <= hard_error_i;
SOFT_ERROR <= soft_error_i;
FRAME_ERROR <= frame_error_i;
CHANNEL_UP <= channel_up_i;

power_down <= gnd;
warn_cc <= gnd;

-- Clock compensation cycles generator
process(RESET, aur_clk)
begin
   if (RESET = '1') then
      cnt_cc_gap <= (others => '0');
   elsif (aur_clk'event AND aur_clk = '1') then
      if (cnt_cc_gap_ovf = '1') then
         cnt_cc_gap <= (others => '0');
      elsif (reg_do_cc = '0') then
         cnt_cc_gap <= cnt_cc_gap + 1;
      end if;
   end if;
end process;

process(RESET, aur_clk)
begin
   if (RESET = '1') then
      cnt_cc_cycles <= (others => '0');
   elsif (aur_clk'event AND aur_clk = '1') then
      if (cnt_cc_cycles_ovf = '1') then
         cnt_cc_cycles <= (others => '0');
      elsif (reg_do_cc = '1') then
         cnt_cc_cycles <= cnt_cc_cycles + 1;
      end if;
   end if;
end process;

lanes2_cc_gen: if (DATA_PATHS/LANES = 2) generate
   cnt_cc_gap_warn <= '1' when cnt_cc_gap = "1001110000011" else -- 4995
                      '0';
   cnt_cc_gap_ovf <= '1' when cnt_cc_gap = "1001110000111" else -- 4999
                     '0';
   cnt_cc_cycles_ovf <= '1' when cnt_cc_cycles = "101" else
                        '0';
end generate;
lanes4_cc_gen: if (DATA_PATHS/LANES = 4) generate
   cnt_cc_gap_warn <= '1' when cnt_cc_gap = "0101110110011" else -- 2995
                      '0';
   cnt_cc_gap_ovf <= '1' when cnt_cc_gap = "0101110110111" else -- 2999
                     '0';
   cnt_cc_cycles_ovf <= '1' when cnt_cc_cycles = "010" else
                        '0';
end generate;

process(RESET, aur_clk)
begin
   if (RESET = '1') then
      reg_warn_cc <= '0';
   elsif (aur_clk'event AND aur_clk = '1') then
      if (cnt_cc_gap_warn = '1') then
         reg_warn_cc <= '1';
      elsif (cnt_cc_gap_ovf = '1') then
         reg_warn_cc <= '0';
      end if;
   end if;
end process;
reg_warn_cc_dly <= reg_warn_cc after 1 ns;

process(RESET, aur_clk)
begin
   if (RESET = '1') then
      reg_chnl_up <= '0';
   elsif (aur_clk'event AND aur_clk = '1') then
      reg_chnl_up <= channel_up_i;
   end if;
end process;
chnl_initialized <= channel_up_i and not reg_chnl_up;

process(RESET, aur_clk)
begin
   if (RESET = '1') then
      reg_do_cc <= '0';
   elsif (aur_clk'event AND aur_clk = '1') then
      if (cnt_cc_gap_ovf = '1' or chnl_initialized = '1') then
         reg_do_cc <= '1';
      elsif (cnt_cc_cycles_ovf = '1') then
         reg_do_cc <= '0';
      end if;
   end if;
end process;
reg_do_cc_dly <= reg_do_cc after 1 ns;

-- RX SOF/EOF generator
output_valid <= rxu_src_rdy_n nor RX_DST_RDY_N;
SOF_EOF_generator_u : SOF_EOF_generator
   generic map(
      RX_IS_HEADER      => RX_IS_HEADER,
      RX_IS_FOOTER      => RX_IS_FOOTER
   )   
   port map(
      -- Common Input
      RESET          => RESET,
      CLK            => CMDCLK,
      EN             => output_valid,

      -- RX SOP/EOP signals
      RX_SOP_N       => rxu_sop_n,
      RX_EOP_N       => rxu_eop_n,

      -- Generated EX SOF/EOF signals
      RX_SOF_N       => RX_SOF_N,
      RX_EOF_N       => RX_EOF_N
   );

end behavioral;






