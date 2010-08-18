
-- aurvc_core.vhd: Aurora with Virtual Channels - the core
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


-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of aurvc_core is

component tx_chnl_ctrl is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNELS             : integer      -- Number of channels
   );
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Data Multiplexers Control
      TX_IFC_ID         : out std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);
      DATA_ID_MX        : out std_logic;

      -- Buffer Control Interface
      FIFO_READ         : out std_logic;
      FIFO_DV           : in std_logic;
      FIFO_EOP          : in std_logic;
      FIFO_EMPTY        : in std_logic;
      BYTE_QUOTA_MET    : in std_logic;
      BYTE_QUOTA_RST    : out std_logic;
      FIFO_EMPTY_VECTOR : in std_logic_vector(CHANNELS-1 downto 0);

      -- Aurora LocalLink Interface
      TX_SRC_RDY_N      : out std_logic;
      TX_SOF_N          : out std_logic;
      TX_EOF_N          : out std_logic;
      TX_DST_RDY_N      : in std_logic;

      -- Aurora UFC RX Interface
      UFC_RX_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_RX_SRC_RDY_N  : in std_logic;
      UFC_RX_SOF_N      : in std_logic;
      UFC_RX_EOF_N      : in std_logic;
      UFC_RX_REM        : in std_logic_vector(log2(DATA_PATHS)-1 downto 0)
   );
end component;

component rx_chnl_ctrl is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNELS             : integer      -- Number of channels
   );
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Data Multiplexers Control
      RX_IFC_ID         : out std_logic_vector(max(log2(CHANNELS)-1, 0) downto 0);

      -- RX Buffer Control Interface
      FIFO_WRITE        : out std_logic;
      FIFO_ALMOST_FULL  : in std_logic_vector(CHANNELS-1 downto 0);

      -- Aurora LocalLink RX Interface
      RX_D              : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_SRC_RDY_N      : in std_logic;
      RX_SOF_N          : in std_logic;
      RX_EOF_N          : in std_logic;

      -- Aurora UFC TX Inteface
      UFC_TX_DATA      : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_TX_REQ_N     : out std_logic;
      UFC_TX_MS        : out std_logic_vector(0 to 2);
      UFC_TX_ACK_N     : in std_logic
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

-- common signals
signal gnd     : std_logic;
signal pwr     : std_logic;
signal aur_clk : std_logic;

-- Aurora signals
-- TX
signal txa_d    :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal txa_d_i     : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal txa_d_i2    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal txa_d_rev   : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal txa_d_rev_i : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal txa_rem_rev : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
signal txa_rem     :  std_logic_vector(0 to log2(DATA_PATHS)-1);
signal txa_src_rdy_n     :  std_logic;
signal txa_sof_n      :  std_logic;
signal txa_eof_n      :  std_logic;
signal txa_dst_rdy_n     :  std_logic;
-- RX
signal rxa_d    :  std_logic_vector(0 to (DATA_PATHS*8)-1);
signal rxa_d_rev   : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal rxa_d_rev_i : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal rxa_rem_rev : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
signal rxa_rem     :  std_logic_vector(0 to log2(DATA_PATHS)-1);
signal rxa_src_rdy_n     :  std_logic;
signal rxa_sof_n : std_logic;
signal rxa_eof_n : std_logic;

signal channel_up_i : std_logic;
signal reg_chnl_up  : std_logic;
signal warn_cc : std_logic;
signal do_cc : std_logic;
signal power_down : std_logic;

signal ufc_tx_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal ufc_tx_req_n : std_logic;
signal ufc_tx_ms : std_logic_vector(2 downto 0);
signal ufc_tx_ack_n : std_logic;

signal ufc_rx_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal ufc_rx_rem : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
signal ufc_rx_src_rdy_n : std_logic;
signal ufc_rx_sof_n : std_logic;
signal ufc_rx_eof_n : std_logic;

-- Multiplexers
signal tx_ifc_id : std_logic_vector(max(log2(TX_CHANNELS)-1, 0) downto 0);
signal tx_ifc_id_i : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal data_id_mx : std_logic;
signal rx_ifc_id : std_logic_vector(max(log2(RX_CHANNELS)-1, 0) downto 0);

-- Buffer control
signal txfifo_read : std_logic;
signal txfifo_dv : std_logic;
signal txfifo_eop : std_logic;
signal txfifo_empty : std_logic;
signal txfifo_byte_quota_met : std_logic;
signal txfifo_byte_quota_rst : std_logic;
signal rxfifo_write : std_logic;

-- Pipeline registers
signal reg_txfifo_byte_quota_met : std_logic;

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

non_twobyte_aurora_inst_gen: if (DATA_PATHS/LANES > 2) generate
   aur_clk <= USRCLK2;
end generate;

-- -------------------------------------------------------------
-- Aurora module
   
-- Remap Big Endian <-> Little Endian
to_little_endian_gen: for i in 0 to (DATA_PATHS)-1 generate
   txa_d_rev_i(((i+1)*8)-1 downto i*8) <= txa_d_rev((((DATA_PATHS)-i)*8)-1 downto ((DATA_PATHS)-i-1)*8);
   rxa_d_rev(((i+1)*8)-1 downto i*8)   <= rxa_d_rev_i((((DATA_PATHS)-i)*8)-1 downto ((DATA_PATHS)-i-1)*8);
end generate;

-- txa_d_rev_i/ufc_tx_data multiplexer
txa_d <= txa_d_rev_i when txa_dst_rdy_n = '0' else
         ufc_tx_data;

rxa_d_rev_i <= rxa_d;

txa_rem     <= txa_rem_rev;
rxa_rem_rev <= rxa_rem;

rio_aurora_module_u: rio_aurora_module
    generic map(
         LANES             => LANES,     -- Number of lanes 
         DATA_PATHS        => DATA_PATHS -- Number of data paths
    )
    port map(
            -- LocalLink TX Interface
            TX_D             => txa_d,
            TX_REM           => txa_rem,
            TX_SRC_RDY_N     => txa_src_rdy_n,
            TX_SOF_N         => txa_sof_n,
            TX_EOF_N         => txa_eof_n,
            TX_DST_RDY_N     => txa_dst_rdy_n,

            -- LocalLink RX Interface
            RX_D             => rxa_d,
            RX_REM           => rxa_rem,
            RX_SRC_RDY_N     => rxa_src_rdy_n,
            RX_SOF_N         => rxa_sof_n,
            RX_EOF_N         => rxa_eof_n,

            -- Native Flow Control Interface

            NFC_REQ_N        => '1',
            NFC_NB           => "0000",
            NFC_ACK_N        => open,

            -- User Flow Control TX Interface

            UFC_TX_REQ_N     => ufc_tx_req_n,
            UFC_TX_MS        => ufc_tx_ms,
            UFC_TX_ACK_N     => ufc_tx_ack_n,

            -- User Flow Control RX Inteface

            UFC_RX_DATA      => ufc_rx_data,
            UFC_RX_REM       => ufc_rx_rem,
            UFC_RX_SRC_RDY_N => ufc_rx_src_rdy_n,
            UFC_RX_SOF_N     => ufc_rx_sof_n,
            UFC_RX_EOF_N     => ufc_rx_eof_n,

            -- MGT Serial I/O
            RXP              => RXP,
            RXN              => RXN,
            TXP              => TXP,
            TXN              => TXN,

            -- MGT Reference Clock Interface
            TOP_REF_CLK      => REFCLK,

            -- Error Detection Interface
            HARD_ERROR       => HARD_ERROR,
            SOFT_ERROR       => SOFT_ERROR,
            FRAME_ERROR      => FRAME_ERROR,

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

CHANNEL_UP <= channel_up_i;
power_down <= gnd;

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

-- -------------------------------------------------------------
-- TX Channel Controler
tx_chnl_ctrl_u: tx_chnl_ctrl
   generic map(
      DATA_PATHS           => DATA_PATHS,
      CHANNELS             => TX_CHANNELS
   )
   port map(
      -- Common Interface
      CLK               => aur_clk,
      RESET             => RESET,

      -- Data Multiplexers Control
      TX_IFC_ID         => tx_ifc_id,
      DATA_ID_MX        => data_id_mx,

      -- Buffer Control Interface
      FIFO_READ         => txfifo_read,
      FIFO_DV           => txfifo_dv,
      FIFO_EOP          => txfifo_eop,
      FIFO_EMPTY        => txfifo_empty,
      BYTE_QUOTA_MET    => reg_txfifo_byte_quota_met,
      BYTE_QUOTA_RST    => txfifo_byte_quota_rst,
      FIFO_EMPTY_VECTOR => TX_BUFFER_EMPTY,

      -- Aurora LocalLink Interface
      TX_SRC_RDY_N      => txa_src_rdy_n,
      TX_SOF_N          => txa_sof_n,
      TX_EOF_N          => txa_eof_n,
      TX_DST_RDY_N      => txa_dst_rdy_n,

      -- Aurora UFC RX Interface
      UFC_RX_DATA       => ufc_rx_data,
      UFC_RX_SRC_RDY_N  => ufc_rx_src_rdy_n,
      UFC_RX_SOF_N      => ufc_rx_sof_n,
      UFC_RX_EOF_N      => ufc_rx_eof_n,
      UFC_RX_REM        => ufc_rx_rem
   );

-- -------------------------------------------------------------
-- TX Multiplexers

-- TX Buffer data & control multiplexer
process (tx_ifc_id, TX_BUFFER_DATA, TX_BUFFER_REM, txfifo_read, TX_BUFFER_DV, TX_BUFFER_EOP, TX_BUFFER_EMPTY, BYTE_QUOTA_MET, txfifo_byte_quota_rst)
begin
   txa_d_i              <= (others => '0');
   txa_rem_rev          <= (others => '0');
   TX_BUFFER_READ         <= (others => '0');
   txfifo_dv              <= '0';
   txfifo_eop             <= '0';
   txfifo_empty           <= '0';
   txfifo_byte_quota_met  <= '0';
   BYTE_QUOTA_RST         <= (others => '0');

   for i in 0 to TX_CHANNELS-1 loop
      if (tx_ifc_id = conv_std_logic_vector(i,max(log2(TX_CHANNELS), 1))) then
         txa_d_i           <= TX_BUFFER_DATA((DATA_PATHS*8*(i+1))- 1 downto (DATA_PATHS*8*i));
         txa_rem_rev         <= TX_BUFFER_REM((log2(DATA_PATHS)*(i+1))-1 downto log2(DATA_PATHS)*i);
         TX_BUFFER_READ(i)   <= txfifo_read;
         txfifo_dv           <= TX_BUFFER_DV(i);
         txfifo_eop          <= TX_BUFFER_EOP(i);
         txfifo_empty        <= TX_BUFFER_EMPTY(i);
         txfifo_byte_quota_met <= BYTE_QUOTA_MET(i);
         BYTE_QUOTA_RST(i) <= txfifo_byte_quota_rst;
      end if;
   end loop;

end process;

tx_ifc_id_i_gen: for i in 0 to (DATA_PATHS*8)-1 generate
   tx_ifc_id_asgn_gen: if (i < log2(TX_CHANNELS)) generate
      tx_ifc_id_i(i) <= tx_ifc_id(i);
   end generate;
   zero_asgn_gen: if (i >= log2(TX_CHANNELS)) generate
      tx_ifc_id_i(i) <= '0';
   end generate;
end generate;

-- Data/ID multiplexer
txa_d_rev <= tx_ifc_id_i when data_id_mx = '1' else
             txa_d_i;


-- This register was added to improve net timing
process(RESET, aur_clk)
begin
   if (RESET = '1') then
      reg_txfifo_byte_quota_met <= '0';
   elsif (aur_clk'event AND aur_clk = '1') then
      reg_txfifo_byte_quota_met <= txfifo_byte_quota_met;
   end if;
end process;

-- -------------------------------------------------------------
-- RX Channel Controler
rx_chnl_ctrl_u: rx_chnl_ctrl
   generic map(
      DATA_PATHS           => DATA_PATHS,
      CHANNELS             => RX_CHANNELS
   )
   port map(
      -- Common Interface
      CLK               => aur_clk,
      RESET             => RESET,

      -- Data Multiplexers Control
      RX_IFC_ID         => rx_ifc_id,

      -- RX Buffer Control Interface
      FIFO_WRITE        => rxfifo_write,
      FIFO_ALMOST_FULL  => RX_BUFFER_ALMOST_FULL,

      -- Aurora LocalLink RX Interface
      RX_D              => rxa_d,
      RX_SRC_RDY_N      => rxa_src_rdy_n,
      RX_SOF_N          => rxa_sof_n,
      RX_EOF_N          => rxa_eof_n,

      -- Aurora UFC TX Inteface
      UFC_TX_DATA      => ufc_tx_data,
      UFC_TX_REQ_N     => ufc_tx_req_n,
      UFC_TX_MS        => ufc_tx_ms,
      UFC_TX_ACK_N     => ufc_tx_ack_n
   );

-- -------------------------------------------------------------
-- RX Multiplexers

-- RX Buffer data & control multiplexer
process (rx_ifc_id, rxfifo_write)
begin
   RX_BUFFER_WRITE        <= (others => '0');

   for i in 0 to RX_CHANNELS-1 loop
      if (rx_ifc_id = conv_std_logic_vector(i,max(log2(RX_CHANNELS), 1))) then
         RX_BUFFER_WRITE(i)  <= rxfifo_write;
      end if;
   end loop;

end process;

BUFFER_CLK <= aur_clk;
RX_BUFFER_DATA <= rxa_d_rev;
RX_BUFFER_REM  <= rxa_rem_rev;
RX_BUFFER_EOP  <= not rxa_eof_n;

end behavioral;


