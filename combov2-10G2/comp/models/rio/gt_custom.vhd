
-- gt_custom.vhd: Simulation model for GT_CUSTOM RocketIO MGT
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

entity GT_CUSTOM is
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
end GT_CUSTOM;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of GT_CUSTOM is

component GT_MODEL is
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
end component;

begin

GT_MODEL_U: GT_MODEL
    generic map ( 
       ALIGN_COMMA_MSB => ALIGN_COMMA_MSB,
       CHAN_BOND_LIMIT => CHAN_BOND_LIMIT,
       CHAN_BOND_MODE => CHAN_BOND_MODE,
       CHAN_BOND_OFFSET => CHAN_BOND_OFFSET,
       CHAN_BOND_ONE_SHOT => CHAN_BOND_ONE_SHOT,
       CHAN_BOND_SEQ_1_1 => CHAN_BOND_SEQ_1_1,
       CHAN_BOND_SEQ_1_2 => CHAN_BOND_SEQ_1_2,
       CHAN_BOND_SEQ_1_3 => CHAN_BOND_SEQ_1_3,
       CHAN_BOND_SEQ_1_4 => CHAN_BOND_SEQ_1_4,
       CHAN_BOND_SEQ_2_1 => CHAN_BOND_SEQ_2_1,
       CHAN_BOND_SEQ_2_2 => CHAN_BOND_SEQ_2_2,
       CHAN_BOND_SEQ_2_3 => CHAN_BOND_SEQ_2_3,
       CHAN_BOND_SEQ_2_4 => CHAN_BOND_SEQ_2_4,
       CHAN_BOND_SEQ_2_USE => CHAN_BOND_SEQ_2_USE,
       CHAN_BOND_SEQ_LEN => CHAN_BOND_SEQ_LEN,
       CHAN_BOND_WAIT => CHAN_BOND_WAIT,
       CLK_CORRECT_USE => CLK_CORRECT_USE,
       CLK_COR_INSERT_IDLE_FLAG => CLK_COR_INSERT_IDLE_FLAG,
       CLK_COR_KEEP_IDLE => CLK_COR_KEEP_IDLE,
       CLK_COR_REPEAT_WAIT => CLK_COR_REPEAT_WAIT,
       CLK_COR_SEQ_1_1 => CLK_COR_SEQ_1_1,
       CLK_COR_SEQ_1_2 => CLK_COR_SEQ_1_2,
       CLK_COR_SEQ_1_3 => CLK_COR_SEQ_1_3,
       CLK_COR_SEQ_1_4 => CLK_COR_SEQ_1_4,
       CLK_COR_SEQ_2_1 => CLK_COR_SEQ_2_1,
       CLK_COR_SEQ_2_2 => CLK_COR_SEQ_2_2,
       CLK_COR_SEQ_2_3 => CLK_COR_SEQ_2_3,
       CLK_COR_SEQ_2_4 => CLK_COR_SEQ_2_4,
       CLK_COR_SEQ_2_USE => CLK_COR_SEQ_2_USE,
       CLK_COR_SEQ_LEN => CLK_COR_SEQ_LEN,
       COMMA_10B_MASK => COMMA_10B_MASK,
       CRC_END_OF_PKT => CRC_END_OF_PKT,
       CRC_FORMAT => CRC_FORMAT,
       CRC_START_OF_PKT => CRC_START_OF_PKT,
       DEC_MCOMMA_DETECT => DEC_MCOMMA_DETECT,
       DEC_PCOMMA_DETECT => DEC_PCOMMA_DETECT,
       DEC_VALID_COMMA_ONLY => DEC_VALID_COMMA_ONLY,
       MCOMMA_10B_VALUE => MCOMMA_10B_VALUE,
       MCOMMA_DETECT => MCOMMA_DETECT,
       PCOMMA_10B_VALUE => PCOMMA_10B_VALUE,
       PCOMMA_DETECT => PCOMMA_DETECT,
       RX_BUFFER_USE => RX_BUFFER_USE,
       RX_CRC_USE => RX_CRC_USE,
       RX_DATA_WIDTH => RX_DATA_WIDTH,
       RX_DECODE_USE => RX_DECODE_USE,
       RX_LOSS_OF_SYNC_FSM => RX_LOSS_OF_SYNC_FSM,
       RX_LOS_INVALID_INCR => RX_LOS_INVALID_INCR,
       RX_LOS_THRESHOLD => RX_LOS_THRESHOLD,
       TERMINATION_IMP => TERMINATION_IMP,
       SERDES_10B => SERDES_10B,
       TX_BUFFER_USE => TX_BUFFER_USE,
       TX_CRC_FORCE_VALUE => TX_CRC_FORCE_VALUE,
       TX_CRC_USE => TX_CRC_USE,
       TX_DATA_WIDTH => TX_DATA_WIDTH,
       TX_DIFF_CTRL => TX_DIFF_CTRL,
       TX_PREEMPHASIS => TX_PREEMPHASIS,
       REF_CLK_V_SEL => REF_CLK_V_SEL
    )
    port map(
       CHBONDI        => CHBONDI,
       CONFIGENABLE   => CONFIGENABLE,
       CONFIGIN       => CONFIGIN,
       ENMCOMMAALIGN  => ENMCOMMAALIGN,
       ENPCOMMAALIGN  => ENPCOMMAALIGN,
       ENCHANSYNC     => ENCHANSYNC,
       LOOPBACK       => LOOPBACK,
       POWERDOWN      => POWERDOWN,
       REFCLK         => REFCLK,
       REFCLK2        => REFCLK2,
       REFCLKSEL      => REFCLKSEL,
       BREFCLK        => BREFCLK,
       BREFCLK2       => BREFCLK2,
       RXN            => RXN,
       RXP            => RXP,
       RXPOLARITY     => RXPOLARITY,
       RXRESET        => RXRESET,
       RXUSRCLK       => RXUSRCLK,
       RXUSRCLK2      => RXUSRCLK2,
       TXBYPASS8B10B  => TXBYPASS8B10B,
       TXCHARDISPMODE => TXCHARDISPMODE,
       TXCHARDISPVAL  => TXCHARDISPVAL,
       TXCHARISK      => TXCHARISK,
       TXDATA         => TXDATA,
       TXFORCECRCERR  => TXFORCECRCERR,
       TXINHIBIT      => TXINHIBIT,
       TXPOLARITY     => TXPOLARITY,
       TXRESET        => TXRESET,
       TXUSRCLK       => TXUSRCLK,
       TXUSRCLK2      => TXUSRCLK2,
       CHBONDDONE     => CHBONDDONE,
       CHBONDO        => CHBONDO,
       CONFIGOUT      => CONFIGOUT,
       RXBUFSTATUS    => RXBUFSTATUS,
       RXCHARISCOMMA  => RXCHARISCOMMA,
       RXCHARISK      => RXCHARISK,
       RXCHECKINGCRC  => RXCHECKINGCRC,
       RXCLKCORCNT    => RXCLKCORCNT,
       RXCOMMADET     => RXCOMMADET,
       RXCRCERR       => RXCRCERR,
       RXDATA         => RXDATA,
       RXDISPERR      => RXDISPERR,
       RXLOSSOFSYNC   => RXLOSSOFSYNC,
       RXNOTINTABLE   => RXNOTINTABLE,
       RXREALIGN      => RXREALIGN,
       RXRECCLK       => RXRECCLK,
       RXRUNDISP      => RXRUNDISP,
       TXBUFERR       => TXBUFERR,
       TXKERR         => TXKERR,
       TXN            => TXN,
       TXP            => TXP,
       TXRUNDISP      => TXRUNDISP
   );

end behavioral;



