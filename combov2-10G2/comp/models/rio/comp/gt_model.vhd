
-- gt_model.vhd: Mutli Gigabit Transceiver model 
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
use work.riosim_pkg.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity GT_MODEL is
    generic ( 
       ALIGN_COMMA_MSB : boolean :=  FALSE;
       CHAN_BOND_LIMIT : integer :=  16;
       CHAN_BOND_MODE : string :=  "OFF";
       CHAN_BOND_OFFSET : integer :=  8;
       CHAN_BOND_ONE_SHOT : boolean :=  FALSE;
       CHAN_BOND_SEQ_1_1 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_1_2 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_1_3 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_1_4 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_2_1 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_2_2 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_2_3 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_2_4 : bit_vector :=  "00000000000";
       CHAN_BOND_SEQ_2_USE : boolean :=  FALSE;
       CHAN_BOND_SEQ_LEN : integer :=  1;
       CHAN_BOND_WAIT : integer :=  8;
       CLK_CORRECT_USE : boolean :=  TRUE;
       CLK_COR_INSERT_IDLE_FLAG : boolean :=  FALSE;
       CLK_COR_KEEP_IDLE : boolean :=  FALSE;
       CLK_COR_REPEAT_WAIT : integer :=  1;
       CLK_COR_SEQ_1_1 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_1_2 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_1_3 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_1_4 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_2_1 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_2_2 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_2_3 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_2_4 : bit_vector :=  "00000000000";
       CLK_COR_SEQ_2_USE : boolean :=  FALSE;
       CLK_COR_SEQ_LEN : integer :=  1;
       COMMA_10B_MASK : bit_vector :=  "1111111000";
       CRC_END_OF_PKT : string :=  "K29_7";
       CRC_FORMAT : string :=  "USER_MODE";
       CRC_START_OF_PKT : string :=  "K27_7";
       DEC_MCOMMA_DETECT : boolean :=  TRUE;
       DEC_PCOMMA_DETECT : boolean :=  TRUE;
       DEC_VALID_COMMA_ONLY : boolean :=  TRUE;
       MCOMMA_10B_VALUE : bit_vector :=  "1100000000";
       MCOMMA_DETECT : boolean :=  TRUE;
       PCOMMA_10B_VALUE : bit_vector :=  "0011111000";
       PCOMMA_DETECT : boolean :=  TRUE;
       RX_BUFFER_USE : boolean :=  TRUE;
       RX_CRC_USE : boolean :=  FALSE;
       RX_DATA_WIDTH : integer :=  2;
       RX_DECODE_USE : boolean :=  TRUE;
       RX_LOSS_OF_SYNC_FSM : boolean :=  TRUE;
       RX_LOS_INVALID_INCR : integer :=  1;
       RX_LOS_THRESHOLD : integer :=  4;
       TERMINATION_IMP : integer :=  50;
       SERDES_10B : boolean :=  FALSE;
       TX_BUFFER_USE : boolean :=  TRUE;
       TX_CRC_FORCE_VALUE : bit_vector :=  "11010110";
       TX_CRC_USE : boolean :=  FALSE;
       TX_DATA_WIDTH : integer :=  2;
       TX_DIFF_CTRL : integer :=  500;
       TX_PREEMPHASIS : integer :=  0;
       REF_CLK_V_SEL : integer :=  0
    );
    port (
       CHBONDI        : in    std_logic_vector (3 downto 0); 
       CONFIGENABLE   : in    std_logic;
       CONFIGIN       : in    std_logic;
       ENMCOMMAALIGN  : in    std_logic;
       ENPCOMMAALIGN  : in    std_logic;
       ENCHANSYNC     : in    std_logic; 
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
       TXBYPASS8B10B  : in    std_logic_vector (TX_DATA_WIDTH-1 downto 0);
       TXCHARDISPMODE : in    std_logic_vector (TX_DATA_WIDTH-1 downto 0);
       TXCHARDISPVAL  : in    std_logic_vector (TX_DATA_WIDTH-1 downto 0);
       TXCHARISK      : in    std_logic_vector (TX_DATA_WIDTH-1 downto 0);
       TXDATA         : in    std_logic_vector ((TX_DATA_WIDTH*8)-1 downto 0);
       TXFORCECRCERR  : in    std_logic;
       TXINHIBIT      : in    std_logic;
       TXPOLARITY     : in    std_logic;
       TXRESET        : in    std_logic;
       TXUSRCLK       : in    std_logic;
       TXUSRCLK2      : in    std_logic;
       CHBONDDONE     : out   std_logic; 
       CHBONDO        : out   std_logic_vector (3 downto 0); 
       CONFIGOUT      : out   std_logic;
       RXBUFSTATUS    : out   std_logic_vector (1 downto 0);
       RXCHARISCOMMA  : out   std_logic_vector (RX_DATA_WIDTH-1 downto 0);
       RXCHARISK      : out   std_logic_vector (RX_DATA_WIDTH-1 downto 0);
       RXCHECKINGCRC  : out   std_logic;
       RXCLKCORCNT    : out   std_logic_vector (2 downto 0);
       RXCOMMADET     : out   std_logic;
       RXCRCERR       : out   std_logic;
       RXDATA         : out   std_logic_vector ((RX_DATA_WIDTH*8)-1 downto 0);
       RXDISPERR      : out   std_logic_vector (RX_DATA_WIDTH-1 downto 0);
       RXLOSSOFSYNC   : out   std_logic_vector (1 downto 0);
       RXNOTINTABLE   : out   std_logic_vector (RX_DATA_WIDTH-1 downto 0);
       RXREALIGN      : out   std_logic;
       RXRECCLK       : out   std_logic;
       RXRUNDISP      : out   std_logic_vector (RX_DATA_WIDTH-1 downto 0);
       TXBUFERR       : out   std_logic;
       TXKERR         : out   std_logic_vector (TX_DATA_WIDTH-1 downto 0);
       TXN            : out   std_logic;
       TXP            : out   std_logic;
       TXRUNDISP      : out   std_logic_vector (TX_DATA_WIDTH-1 downto 0)
   );
end GT_MODEL;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of GT_MODEL is

component clk_multiplier is
   port ( 
          CLKIN_IN        : in    std_logic; 
          RST_IN          : in    std_logic; 
          CLKFX_OUT       : out   std_logic; 
          CLK0_OUT        : out   std_logic; 
          LOCKED_OUT      : out   std_logic
   );
end component;

component asfifo is
   generic(
      -- Data Width
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE : integer := 16;

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH : integer
   );
   port(
      RESET    : in  std_logic;

      -- Write interface
      CLK_WR   : in  std_logic;
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      WR       : in  std_logic;
      FULL     : out std_logic;
      STATUS      : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      CLK_RD   : in  std_logic;
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD       : in  std_logic;
      EMPTY    : out std_logic
   );
end component asfifo;

component dual_enc_8b10b is
   port (
      CLK0        : in  std_logic;
      RESET0      : in  std_logic;
      DIN0        : in  std_logic_vector(7 downto 0);
      KIN0        : in  std_logic;
      DISP_IN0    : in  std_logic;
      FORCE_DISP0 : in  std_logic;
      DOUT0       : out std_logic_vector(9 downto 0);
      DISP_OUT0   : out std_logic;
      KERR0       : out std_logic;

      CLK1        : in  std_logic;
      RESET1      : in  std_logic;
      DIN1        : in  std_logic_vector(7 downto 0);
      KIN1        : in  std_logic;
      DISP_IN1    : in  std_logic;
      FORCE_DISP1 : in  std_logic;
      DOUT1       : out std_logic_vector(9 downto 0);
      DISP_OUT1   : out std_logic;
      KERR1       : out std_logic
   );
end component;

component dual_dec_8b10b is
   port (
      CLK0      : in  std_logic;
      RESET0    : in  std_logic;
      DIN0      : in  std_logic_vector(9 downto 0);
      DOUT0     : out std_logic_vector(7 downto 0);
      K0        : out std_logic;
      INVALID0  : out std_logic;

      CLK1      : in  std_logic;
      RESET1    : in  std_logic;
      DIN1      : in  std_logic_vector(9 downto 0);
      DOUT1     : out std_logic_vector(7 downto 0);
      K1        : out std_logic;
      INVALID1  : out std_logic
   );
end component;

component tx_buf_fsm is
   port (
      -- Common interface
      RESET    : in std_logic;
      CLK      : in std_logic;

      -- Input
      RD       : in std_logic;
      EMPTY    : in std_logic;

      -- Output
      DV       : out std_logic;
      IDLE     : out std_logic
   );
end component;

   -- Reset signals
   signal reset_i : std_logic;
   signal rst     : std_logic;
   signal nrst    : std_logic;

   -- Clocks
   signal rioclk_i : std_logic;
   signal rioclk  : std_logic;
   signal serclk  : std_logic;
   signal txclk   : std_logic;
   signal rxclk   : std_logic;

   -- TX Buffer
--   signal txfifo_di_rev : std_logic_vector((TX_DATA_WIDTH*10)-1 downto 0);
   signal txfifo_di : std_logic_vector((TX_DATA_WIDTH*10)-1 downto 0);
   signal txfifo_wr : std_logic;
   signal txfifo_rd : std_logic;
   signal txfifo_full : std_logic;
   signal txfifo_do : std_logic_vector((TX_DATA_WIDTH*10)-1 downto 0);
   signal txfifo_empty : std_logic;
   signal reg_txfifo_full : std_logic;
   signal idle_mx    : std_logic;
   
   -- RX Buffer
   signal rxfifo_di : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
   signal rxfifo_wr : std_logic;
   signal rxfifo_full : std_logic;
   signal rxfifo_status : std_logic_vector(3 downto 0);
   signal rxfifo_do : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
   signal rxfifo_empty : std_logic;
   
   -- TX serialization
   signal sreg_txdata   : std_logic_vector((TX_DATA_WIDTH*10)-1 downto 0);
   signal sreg_txdata_ce: std_logic;
   signal stxdata : std_logic_vector((TX_DATA_WIDTH*10)-1 downto 0);

   -- TX 8/10 coding
   signal txrundisp_i : std_logic_vector(TX_DATA_WIDTH-1 downto 0);
   signal tx_riodata : std_logic_vector((TX_DATA_WIDTH*8)-1 downto 0);
   signal tx_riodataisk : std_logic_vector((TX_DATA_WIDTH)-1 downto 0);

   -- RX comma detection
   signal pcommadet_i_algn : std_logic;
   signal mcommadet_i_algn : std_logic;
   signal pcommadet : std_logic;
   signal mcommadet : std_logic;
   signal pcommadet_i : std_logic;
   signal mcommadet_i : std_logic;
   signal dec_pcommadet : std_logic_vector((RX_DATA_WIDTH)-1 downto 0);
   signal dec_mcommadet : std_logic_vector((RX_DATA_WIDTH)-1 downto 0);

   -- RX deserialization
   signal sreg_rxdata : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
   signal cnt_deser_lock_allowed : std_logic_vector(4 downto 0);
   signal reg_deser_lock_allowed : std_logic;
   signal reg_deser_lock_allowed_set : std_logic;
   signal deser_lock_allowed : std_logic;
   signal reg_rx_deser_lock : std_logic;
   signal rx_deser_lock_set : std_logic;
   signal drxdata : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
--   signal drxdata_rev : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
   signal reg_drxdata : std_logic_vector((RX_DATA_WIDTH*10)-1 downto 0);
   signal drxdata_ce : std_logic;
   signal cnt_val : std_logic_vector(5 downto 0);
   signal cnt_srxdata : std_logic_vector(5 downto 0);
   signal cnt_srxdata_load : std_logic;
   signal cnt_srxdata_ce : std_logic;
   
   -- RX 8/10 decoding
   signal rx_riodata : std_logic_vector((RX_DATA_WIDTH*8)-1 downto 0);
   signal rx_riodataisk : std_logic_vector((RX_DATA_WIDTH)-1 downto 0);
   signal rxp_i : std_logic;

   -- Channel Bonding
   signal chbonddone_i : std_logic;
   
begin

reset_i <= TXRESET or RXRESET;
txclk   <= TXUSRCLK2;
rxclk   <= RXUSRCLK2;

-- Generate clock for data serialization (div 20)
clk_multiplier_u: clk_multiplier
   port map(
      RST_IN      => reset_i,
      CLKIN_IN    => rioclk_i,
      CLK0_OUT    => rioclk,
      CLKFX_OUT   => serclk,
      LOCKED_OUT  => nrst
   );
rst <= not nrst;

-- clock input selection
refclk_sel_gen: if (REF_CLK_V_SEL = 0) generate
   rioclk_i <= REFCLK when REFCLKSEL = '0' else
               REFCLK2;
end generate;

brefclk_sel_gen: if (REF_CLK_V_SEL = 1) generate
   rioclk_i <= BREFCLK when REFCLKSEL = '0' else
               BREFCLK2;
end generate;

-- -------------------------------------------------------------
-- Transmition part

tx_riodata <= TXDATA;
tx_riodataisk <= TXCHARISK;

dual_enc_8b10b_u: dual_enc_8b10b
   port map(
      CLK0        => txclk,
      RESET0      => rst,
      DIN0        => tx_riodata(7 downto 0),
      KIN0        => tx_riodataisk(0),
      DISP_IN0    => '0',
      FORCE_DISP0 => '0',
      DOUT0       => txfifo_di(9 downto 0),
      DISP_OUT0   => txrundisp_i(0),
      KERR0       => TXKERR(0),

      CLK1        => txclk,
      RESET1      => rst,
      DIN1        => tx_riodata(15 downto 8),
      KIN1        => tx_riodataisk(1),
      DISP_IN1    => '0',
      FORCE_DISP1 => '0',
      DOUT1       => txfifo_di(19 downto 10),
      DISP_OUT1   => txrundisp_i(1),
      KERR1       => TXKERR(1)
   );

next_enc_gen: if (TX_DATA_WIDTH = 4) generate
   dual_enc_8b10b_u2: dual_enc_8b10b
   port map(
      CLK0        => txclk,
      RESET0      => rst,
      DIN0        => tx_riodata(23 downto 16),
      KIN0        => tx_riodataisk(2),
      DISP_IN0    => '0',
      FORCE_DISP0 => '0',
      DOUT0       => txfifo_di(29 downto 20),
      DISP_OUT0   => txrundisp_i(2),
      KERR0       => TXKERR(2),

      CLK1        => txclk,
      RESET1      => rst,
      DIN1        => tx_riodata(31 downto 24),
      KIN1        => tx_riodataisk(3),
      DISP_IN1    => '0',
      FORCE_DISP1 => '0',
      DOUT1       => txfifo_di(39 downto 30),
      DISP_OUT1   => txrundisp_i(3),
      KERR1       => TXKERR(3)
   );
end generate;

--reverse_txfifo_di_gen: for i in 0 to TX_DATA_WIDTH-1 generate
--   gen235: for j in 0 to 9 generate
--      txfifo_di(j+(10*i)) <= txfifo_di_rev((10*(i+1))-j-1);
--   end generate;
--end generate;

TXRUNDISP <= txrundisp_i;

-- TX Async Buffer
tx_asfifo_u: asfifo
   generic map(
      -- Data Width
      DATA_WIDTH  => TX_DATA_WIDTH*10,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS => 32,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE => 16,

      STATUS_WIDTH => 4
   )
   port map(
      RESET    => rst,

      -- Write interface
      CLK_WR   => txclk,
      DI       => txfifo_di,
      WR       => txfifo_wr,
      FULL     => txfifo_full,
      STATUS   => open,

      -- Read interface
      CLK_RD   => rioclk,
      DO       => txfifo_do,
      RD       => txfifo_rd,
      EMPTY    => txfifo_empty
   );

process(rst, txclk)
begin
   if (rst = '1') then
      reg_txfifo_full <= '0';
   elsif (txclk'event AND txclk = '1') then
      if (txfifo_full = '1' and txfifo_wr = '1') then
         reg_txfifo_full <= '1';
      end if;
   end if;
end process;

-- FIXME: txfifo full signal is asserted for one clock cycle after reset-> due to this TXBUFFERR is asserted
--TXBUFERR <= reg_txfifo_full;
TXBUFERR <= '0';

txfifo_wr <= not rst; -- FIXME: clock correction is not working

two_txway_gen: if (TX_DATA_WIDTH = 2) generate
   stxdata <= txfifo_do when txfifo_empty = '0' else
              IDLE_10B;
end generate;
four_txway_gen: if (TX_DATA_WIDTH = 4) generate
   stxdata <= txfifo_do when idle_mx = '0' else
              IDLE_10B & IDLE_10B;
end generate;

two_txway_buffer_read_gen: if (TX_DATA_WIDTH = 2) generate
   txfifo_rd <= '1';
   sreg_txdata_ce <= '1';
end generate;
four_txway_buffer_read_gen: if (TX_DATA_WIDTH = 4) generate
   tx_buf_fsm_u: tx_buf_fsm
   port map(
      -- Common interface
      RESET    => rst,
      CLK      => rioclk,

      -- Input
      RD       => txfifo_rd,
      EMPTY    => txfifo_empty,

      -- Output
      DV       => sreg_txdata_ce,
      IDLE     => idle_mx
   );

   process(rst, rioclk)
   begin
      if (rst = '1') then
         txfifo_rd <= '0';
      elsif(rioclk'event and rioclk = '1') then
         txfifo_rd <= not txfifo_rd;
      end if;
   end process;
end generate;

-- Serialization circuitry
process(rst, serclk, rioclk)
begin
   if (rst = '1') then
      sreg_txdata <= (others => '0');
   elsif (rioclk'event and rioclk = '1') then
      if (sreg_txdata_ce = '1') then
         sreg_txdata <= stxdata;
      end if;
   elsif (serclk'event and serclk = '1') then
      sreg_txdata <= sreg_txdata((TX_DATA_WIDTH*10)-2 downto 0) & '0';
   end if;
end process;

TXP <= sreg_txdata((TX_DATA_WIDTH*10)-1);
TXN <= not sreg_txdata((TX_DATA_WIDTH*10)-1);

-- -------------------------------------------------------------
-- Reception part

-- Deserialization
pcommadet_i_algn <= '1' when bitvect_mask_match(sreg_rxdata((RX_DATA_WIDTH*10)-1 downto (RX_DATA_WIDTH-1)*10), 
                                                PCOMMA_10B_VALUE, 
                                                COMMA_10B_MASK) else
                    '0';
mcommadet_i_algn <= '1' when bitvect_mask_match(sreg_rxdata((RX_DATA_WIDTH*10)-1 downto (RX_DATA_WIDTH-1)*10), 
                                                MCOMMA_10B_VALUE, 
                                                COMMA_10B_MASK) else
                    '0';

two_way_comma_det_gen:  if (RX_DATA_WIDTH = 2) generate
   pcommadet_i <= '1' when (bitvect_mask_match(sreg_rxdata(9 downto 0), PCOMMA_10B_VALUE, COMMA_10B_MASK)) or
                           (bitvect_mask_match(sreg_rxdata(19 downto 10), PCOMMA_10B_VALUE, COMMA_10B_MASK)) else
                  '0';
   mcommadet_i <= '1' when (bitvect_mask_match(sreg_rxdata(9 downto 0), MCOMMA_10B_VALUE, COMMA_10B_MASK)) or 
                           (bitvect_mask_match(sreg_rxdata(19 downto 10), MCOMMA_10B_VALUE, COMMA_10B_MASK)) else
                  '0';
end generate;
four_way_comma_det_gen:  if (RX_DATA_WIDTH = 4) generate
   pcommadet_i <= '1' when (bitvect_mask_match(sreg_rxdata(9 downto 0), PCOMMA_10B_VALUE, COMMA_10B_MASK)) or
                           (bitvect_mask_match(sreg_rxdata(19 downto 10), PCOMMA_10B_VALUE, COMMA_10B_MASK)) or
                           (bitvect_mask_match(sreg_rxdata(29 downto 20), PCOMMA_10B_VALUE, COMMA_10B_MASK)) or
                           (bitvect_mask_match(sreg_rxdata(39 downto 30), PCOMMA_10B_VALUE, COMMA_10B_MASK)) else
                  '0';
   mcommadet_i <= '1' when (bitvect_mask_match(sreg_rxdata(9 downto 0), MCOMMA_10B_VALUE, COMMA_10B_MASK)) or 
                           (bitvect_mask_match(sreg_rxdata(19 downto 10), MCOMMA_10B_VALUE, COMMA_10B_MASK)) or 
                           (bitvect_mask_match(sreg_rxdata(29 downto 20), MCOMMA_10B_VALUE, COMMA_10B_MASK)) or 
                           (bitvect_mask_match(sreg_rxdata(39 downto 30), MCOMMA_10B_VALUE, COMMA_10B_MASK)) else
                  '0';
end generate;

process(rst, serclk)
begin
   if (rst = '1') then
      cnt_deser_lock_allowed <= (others => '0');
   elsif (serclk'event and serclk = '1') then
      cnt_deser_lock_allowed <= cnt_deser_lock_allowed + 1;
   end if;
end process;

reg_deser_lock_allowed_set <= '1' when cnt_deser_lock_allowed = x"14" else
                              '0';

process(rst, serclk)
begin
   if (rst = '1') then
      reg_deser_lock_allowed <= '0';
   elsif (serclk'event and serclk = '1') then
      if (reg_deser_lock_allowed_set = '1') then
         reg_deser_lock_allowed <= '1';
      end if;
   end if;
end process;

deser_lock_allowed <= reg_deser_lock_allowed;

-- Data will be allways 16b aligned - to better IDLE pattern recognition
--rx_deser_lock_set_gent: if (ALIGN_COMMA_MSB = true) generate
   rx_deser_lock_set <= ((ENPCOMMAALIGN and pcommadet_i_algn) or (ENMCOMMAALIGN and mcommadet_i_algn)) and deser_lock_allowed;
--end generate;
--rx_deser_lock_set_genf: if (ALIGN_COMMA_MSB = false) generate
--   rx_deser_lock_set <= (ENPCOMMAALIGN and pcommadet_i) or (ENMCOMMAALIGN and mcommadet_i);
--end generate;

rxp_i <= RXP when LOOPBACK = "00" else
         sreg_txdata((TX_DATA_WIDTH*10)-1);

process(rst, serclk)
begin
   if (rst = '1') then
      sreg_rxdata <= (others => '0');
   elsif (serclk'event and serclk = '1') then
      sreg_rxdata <= sreg_rxdata((RX_DATA_WIDTH*10)-2 downto 0) & rxp_i;
   end if;
end process;

process(rst, serclk)
begin
   if (rst = '1') then
      reg_rx_deser_lock <= '0';
   elsif (serclk'event AND serclk = '1') then
      if (rx_deser_lock_set = '1') then
         reg_rx_deser_lock <= '1';
      end if;
   end if;
end process;

RXREALIGN <= not reg_rx_deser_lock;

cnt_srxdata_load <= '1' when cnt_srxdata = "000000" else
                    '0';
cnt_srxdata_ce <= reg_rx_deser_lock or rx_deser_lock_set;

two_way_cnt_val_gen: if (RX_DATA_WIDTH = 2) generate
   cnt_val <= "010011";
end generate;
four_way_cnt_val_gen: if (RX_DATA_WIDTH = 4) generate
   cnt_val <= "100111";
end generate;

process(rst, serclk)
begin
   if (rst = '1') then
      cnt_srxdata <= cnt_val;
   elsif (serclk'event AND serclk = '1') then
      if (cnt_srxdata_load = '1') then
         cnt_srxdata <= cnt_val;
      elsif (cnt_srxdata_ce='1') then
         cnt_srxdata <= cnt_srxdata - 1;
      end if;
   end if;
end process;

drxdata_ce <= '1' when (cnt_srxdata = cnt_val) and (cnt_srxdata_ce = '1') else
              '0';
process(rst, serclk)
begin
   if (rst = '1') then
      reg_drxdata <= (others => '0');
   elsif (serclk'event AND serclk = '1') then
      if (drxdata_ce = '1') then
         reg_drxdata <= sreg_rxdata;
      end if;
   end if;
end process;

-- RX Async Buffer
rx_asfifo_u: asfifo
   generic map(
      -- Data Width
      DATA_WIDTH  => RX_DATA_WIDTH*10,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS => 32,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE => 16,

      STATUS_WIDTH => 4
   )
   port map(
      RESET    => rst,

      -- Write interface
      CLK_WR   => rioclk,
      DI       => rxfifo_di,
      WR       => rxfifo_wr,
      FULL     => rxfifo_full,
      STATUS   => rxfifo_status,

      -- Read interface
      CLK_RD   => rxclk,
      DO       => rxfifo_do,
      RD       => '1',
      EMPTY    => rxfifo_empty
   );

rxfifo_di <= reg_drxdata;

two_rxway_buffer_write_gen: if (RX_DATA_WIDTH = 2) generate
   rxfifo_wr <= '0' when is_10b_idle(reg_drxdata) else
                reg_rx_deser_lock;
end generate;
four_rxway_buffer_write_gen: if (RX_DATA_WIDTH = 4) generate
   process(rst, rioclk)
   begin
      if (rst = '1') then
         rxfifo_wr <= '0';
      elsif(rioclk'event and rioclk = '1') then
         if (is_10b_idle(reg_drxdata(39 downto 20)) and is_10b_idle(reg_drxdata(19 downto 0))) then
            rxfifo_wr <= '0';
         elsif (reg_rx_deser_lock = '1') then
            rxfifo_wr <= not rxfifo_wr;
         end if;
      end if;
   end process;
end generate;

RXBUFSTATUS(0) <= rxfifo_status(3); -- Bit 0 indicates that the buffer is at least half-full when asserted High.
RXBUFSTATUS(1) <= rxfifo_full;      -- Buffer overflow 

two_rxway_gen: if (RX_DATA_WIDTH = 2) generate
   drxdata <= rxfifo_do when rxfifo_empty = '0' else
              IDLE_10B;
end generate;
four_rxway_gen: if (RX_DATA_WIDTH = 4) generate
   drxdata <= rxfifo_do when rxfifo_empty = '0' else
              IDLE_10B & IDLE_10B;
end generate;

--reverse_drxdata_gen: for i in 0 to RX_DATA_WIDTH-1 generate
--   gen433: for j in 0 to 9 generate
--      drxdata_rev(j+(10*i)) <= drxdata((10*(i+1))-j-1);
--   end generate;
--end generate;

dual_dec_8b10b_u: dual_dec_8b10b
   port map(
      CLK0      => rxclk,
      RESET0    => rst,
      DIN0      => drxdata(9 downto 0),
      DOUT0     => rx_riodata(7 downto 0),
      K0        => rx_riodataisk(0),
      INVALID0  => open,

      CLK1      => rxclk,
      RESET1    => rst,
      DIN1      => drxdata(19 downto 10),
      DOUT1     => rx_riodata(15 downto 8),
      K1        => rx_riodataisk(1),
      INVALID1  => open
   );
next_dec_gen: if (RX_DATA_WIDTH = 4) generate
   dual_dec_8b10b_u2: dual_dec_8b10b
   port map(
      CLK0      => rxclk,
      RESET0    => rst,
      DIN0      => drxdata(29 downto 20),
      DOUT0     => rx_riodata(23 downto 16),
      K0        => rx_riodataisk(2),
      INVALID0  => open,

      CLK1      => rxclk,
      RESET1    => rst,
      DIN1      => drxdata(39 downto 30),
      DOUT1     => rx_riodata(31 downto 24),
      K1        => rx_riodataisk(3),
      INVALID1  => open
   );
end generate;

-- Due to fake clock correction method the data parity can be wrong
-- But we must pretend, that everything is OK;)
RXNOTINTABLE <= (others => '0');
RXDISPERR <= (others => '0');

RXDATA <= rx_riodata;
RXCHARISK <= rx_riodataisk;

-- RXCHARISCOMMA generation
dec_pcommadet_gent: if (DEC_PCOMMA_DETECT = true) generate
   gen342: for i in 1 to RX_DATA_WIDTH generate
      dec_pcommadet(i-1) <= '1' when (drxdata((i*10)-4 downto (i-1)*10) = "1111100") else
                          '0';
   end generate;
end generate;
dec_pcommadet_genf: if (DEC_PCOMMA_DETECT = false) generate
   dec_pcommadet <= (others => '0');
end generate;

dec_mcommadet_gent: if (DEC_MCOMMA_DETECT = true) generate
   gen4643: for i in 1 to RX_DATA_WIDTH generate
      dec_mcommadet(i-1) <= '1' when (drxdata((i*10)-4 downto (i-1)*10) = "0000011") else
                          '0';
   end generate;
end generate;
dec_mcommadet_genf: if (DEC_MCOMMA_DETECT = false) generate
   dec_mcommadet <= (others => '0');
end generate;

rxchariscomma_gent: if (DEC_VALID_COMMA_ONLY = true) generate
   gen545: for i in 1 to RX_DATA_WIDTH generate
      RXCHARISCOMMA(i-1) <= '1' when (is_comma(rx_riodata((i*8)-1 downto (i-1)*8)) and (rx_riodataisk(i-1) = '1')) else
                            '0';
   end generate;
end generate;
rxchariscomma_genf: if (DEC_VALID_COMMA_ONLY = false) generate
   gen5683: for i in 0 to RX_DATA_WIDTH-1 generate
   
      process(rst, rxclk)
      begin
         if (rst = '1') then
            RXCHARISCOMMA(i) <= '0';
         elsif(rxclk'event and rxclk = '1') then
            RXCHARISCOMMA(i) <= dec_pcommadet(i) or dec_mcommadet(i);
         end if;
      end process;
   
   end generate;
end generate;

-- RXCOMMADET generation
two_way_pcommadet_gent: if (PCOMMA_DETECT = true) and (RX_DATA_WIDTH = 2) generate
pcommadet <= '1' when bitvect_mask_match(drxdata(9 downto 0), PCOMMA_10B_VALUE, COMMA_10B_MASK) or
                      bitvect_mask_match(drxdata(19 downto 10), PCOMMA_10B_VALUE, COMMA_10B_MASK) else
             '0';
end generate;
four_way_pcommadet_gent: if (PCOMMA_DETECT = true) and (RX_DATA_WIDTH = 4) generate
pcommadet <= '1' when bitvect_mask_match(drxdata(9 downto 0), PCOMMA_10B_VALUE, COMMA_10B_MASK) or
                      bitvect_mask_match(drxdata(19 downto 10), PCOMMA_10B_VALUE, COMMA_10B_MASK) or
                      bitvect_mask_match(drxdata(29 downto 20), PCOMMA_10B_VALUE, COMMA_10B_MASK) or
                      bitvect_mask_match(drxdata(39 downto 30), PCOMMA_10B_VALUE, COMMA_10B_MASK) else
             '0';
end generate;
pcommadet_genf: if (PCOMMA_DETECT = false) generate
   pcommadet <= '0';
end generate;

two_way_mcommadet_gent: if (MCOMMA_DETECT = true) and (RX_DATA_WIDTH = 2) generate
mcommadet <= '1' when bitvect_mask_match(drxdata(9 downto 0), MCOMMA_10B_VALUE, COMMA_10B_MASK) or 
                      bitvect_mask_match(drxdata(19 downto 10), MCOMMA_10B_VALUE, COMMA_10B_MASK) else
             '0';
end generate;
four_way_mcommadet_gent: if (MCOMMA_DETECT = true) and (RX_DATA_WIDTH = 4) generate
mcommadet <= '1' when bitvect_mask_match(drxdata(9 downto 0), MCOMMA_10B_VALUE, COMMA_10B_MASK) or 
                      bitvect_mask_match(drxdata(19 downto 10), MCOMMA_10B_VALUE, COMMA_10B_MASK) or 
                      bitvect_mask_match(drxdata(29 downto 20), MCOMMA_10B_VALUE, COMMA_10B_MASK) or 
                      bitvect_mask_match(drxdata(39 downto 30), MCOMMA_10B_VALUE, COMMA_10B_MASK) else
             '0';
end generate;
mcommadet_genf: if (MCOMMA_DETECT = false) generate
   mcommadet <= '0';
end generate;

process(rxclk)
begin
   if (rst = '1') then
      RXCOMMADET <= '0';
   elsif(rxclk'event and rxclk = '1') then
      RXCOMMADET <= pcommadet or mcommadet;
   end if;
end process;

-- Channel bonding fake
-- FIXME: channel bondign working only with 1-word-length channel bond sequences
two_way_chbond_gen: if (TX_DATA_WIDTH = 2) generate
   chbonddone_i <= '0';
end generate;

four_way_chbond_gen: if (TX_DATA_WIDTH = 4) generate
chbonddone_i <= '1' when (drxdata(39 downto 30) = To_StdLogicVector(CHAN_BOND_SEQ_1_1(1 to 10))) else
                '0';
end generate;
CHBONDDONE   <= chbonddone_i and ENCHANSYNC;

process(rst, txclk)
begin
   if (rst = '1') then
      RXCLKCORCNT   <= "000";
   elsif (txclk'event AND txclk = '1') then
      if (chbonddone_i = '1') then
         RXCLKCORCNT   <= "101";
      else
         RXCLKCORCNT   <= "000";
      end if;
   end if;
end process;
         
CHBONDO       <= "0000";

-- Interface mapping
RXRECCLK      <= RXUSRCLK;
CONFIGOUT     <= '0';
RXCHECKINGCRC <= '1';               -- FIXME for CRC check 
RXCRCERR      <= '0';
RXLOSSOFSYNC  <= "00";
RXRUNDISP     <= (others => '0'); -- This should not be necessary to implement

end behavioral;



