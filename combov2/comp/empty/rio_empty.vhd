--
-- rio_empty.vhd: RIO empty entity
--
-- Copyright (C) 2006 CESNET
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
-- $ID:$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.ALL;
use ieee.numeric_std.ALL;
-- synopsys translate_off
library UNISIM;
use UNISIM.Vcomponents.ALL;
-- synopsys translate_on

entity rio_empty is
   port ( 
          RXN       : in    std_logic; 
          RXP       : in    std_logic; 
          TXN       : out   std_logic; 
          TXP       : out   std_logic
        );
end rio_empty;

architecture BEHAVIORAL of rio_empty is
   attribute ALIGN_COMMA_MSB          : string ;
   attribute CHAN_BOND_LIMIT          : string ;
   attribute CHAN_BOND_MODE           : string ;
   attribute CHAN_BOND_OFFSET         : string ;
   attribute CHAN_BOND_ONE_SHOT       : string ;
   attribute CHAN_BOND_SEQ_1_1        : string ;
   attribute CHAN_BOND_SEQ_1_2        : string ;
   attribute CHAN_BOND_SEQ_1_3        : string ;
   attribute CHAN_BOND_SEQ_1_4        : string ;
   attribute CHAN_BOND_SEQ_2_1        : string ;
   attribute CHAN_BOND_SEQ_2_2        : string ;
   attribute CHAN_BOND_SEQ_2_3        : string ;
   attribute CHAN_BOND_SEQ_2_4        : string ;
   attribute CHAN_BOND_SEQ_2_USE      : string ;
   attribute CHAN_BOND_SEQ_LEN        : string ;
   attribute CHAN_BOND_WAIT           : string ;
   attribute CLK_CORRECT_USE          : string ;
   attribute CLK_COR_INSERT_IDLE_FLAG : string ;
   attribute CLK_COR_KEEP_IDLE        : string ;
   attribute CLK_COR_REPEAT_WAIT      : string ;
   attribute CLK_COR_SEQ_1_1          : string ;
   attribute CLK_COR_SEQ_1_2          : string ;
   attribute CLK_COR_SEQ_1_3          : string ;
   attribute CLK_COR_SEQ_1_4          : string ;
   attribute CLK_COR_SEQ_2_1          : string ;
   attribute CLK_COR_SEQ_2_2          : string ;
   attribute CLK_COR_SEQ_2_3          : string ;
   attribute CLK_COR_SEQ_2_4          : string ;
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
   attribute RX_CRC_USE               : string ;
   attribute RX_DATA_WIDTH            : string ;
   attribute RX_DECODE_USE            : string ;
   attribute RX_LOSS_OF_SYNC_FSM      : string ;
   attribute RX_LOS_INVALID_INCR      : string ;
   attribute RX_LOS_THRESHOLD         : string ;
   attribute TERMINATION_IMP          : string ;
   attribute SERDES_10B               : string ;
   attribute TX_BUFFER_USE            : string ;
   attribute TX_CRC_FORCE_VALUE       : string ;
   attribute TX_CRC_USE               : string ;
   attribute TX_DATA_WIDTH            : string ;
   attribute TX_DIFF_CTRL             : string ;
   attribute TX_PREEMPHASIS           : string ;
   attribute REF_CLK_V_SEL            : string ;
   
   signal gnd               : std_logic_vector (31 downto 0);
   signal gnd1              : std_logic;
   signal pwr               : std_logic;
   
   component GT_CUSTOM
      -- synopsys translate_off
      generic( ALIGN_COMMA_MSB : boolean :=  FALSE;
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
               REF_CLK_V_SEL : integer :=  0);
      -- synopsys translate_on
      port ( CHBONDI        : in    std_logic_vector (3 downto 0); 
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
             TXBYPASS8B10B  : in    std_logic_vector (3 downto 0); 
             TXCHARDISPMODE : in    std_logic_vector (3 downto 0); 
             TXCHARDISPVAL  : in    std_logic_vector (3 downto 0); 
             TXCHARISK      : in    std_logic_vector (3 downto 0); 
             TXDATA         : in    std_logic_vector (31 downto 0); 
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
             RXCHARISCOMMA  : out   std_logic_vector (3 downto 0); 
             RXCHARISK      : out   std_logic_vector (3 downto 0); 
             RXCHECKINGCRC  : out   std_logic; 
             RXCLKCORCNT    : out   std_logic_vector (2 downto 0); 
             RXCOMMADET     : out   std_logic; 
             RXCRCERR       : out   std_logic; 
             RXDATA         : out   std_logic_vector (31 downto 0); 
             RXDISPERR      : out   std_logic_vector (3 downto 0); 
             RXLOSSOFSYNC   : out   std_logic_vector (1 downto 0); 
             RXNOTINTABLE   : out   std_logic_vector (3 downto 0); 
             RXREALIGN      : out   std_logic; 
             RXRECCLK       : out   std_logic; 
             RXRUNDISP      : out   std_logic_vector (3 downto 0); 
             TXBUFERR       : out   std_logic; 
             TXKERR         : out   std_logic_vector (3 downto 0); 
             TXN            : out   std_logic; 
             TXP            : out   std_logic; 
             TXRUNDISP      : out   std_logic_vector (3 downto 0));
   end component;
   
   attribute ALIGN_COMMA_MSB of GT_CUSTOM_INST : label is "TRUE";
   attribute CHAN_BOND_LIMIT of GT_CUSTOM_INST : label is "16";
   attribute CHAN_BOND_MODE of GT_CUSTOM_INST : label is "OFF";
   attribute CHAN_BOND_OFFSET of GT_CUSTOM_INST : label is "8";
   attribute CHAN_BOND_ONE_SHOT of GT_CUSTOM_INST : label is "FALSE";
   attribute CHAN_BOND_SEQ_1_1 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_1_2 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_1_3 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_1_4 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_2_1 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_2_2 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_2_3 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_2_4 of GT_CUSTOM_INST : label is "00000000000";
   attribute CHAN_BOND_SEQ_2_USE of GT_CUSTOM_INST : label is "FALSE";
   attribute CHAN_BOND_SEQ_LEN of GT_CUSTOM_INST : label is "1";
   attribute CHAN_BOND_WAIT of GT_CUSTOM_INST : label is "8";
   attribute CLK_CORRECT_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute CLK_COR_INSERT_IDLE_FLAG of GT_CUSTOM_INST : label is "TRUE";
   attribute CLK_COR_KEEP_IDLE of GT_CUSTOM_INST : label is "FALSE";
   attribute CLK_COR_REPEAT_WAIT of GT_CUSTOM_INST : label is "1";
   attribute CLK_COR_SEQ_1_1 of GT_CUSTOM_INST : label is "00110111100";
   attribute CLK_COR_SEQ_1_2 of GT_CUSTOM_INST : label is "00001010000";
   attribute CLK_COR_SEQ_1_3 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_1_4 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_2_1 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_2_2 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_2_3 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_2_4 of GT_CUSTOM_INST : label is "00000000000";
   attribute CLK_COR_SEQ_2_USE of GT_CUSTOM_INST : label is "FALSE";
   attribute CLK_COR_SEQ_LEN of GT_CUSTOM_INST : label is "2";
   attribute COMMA_10B_MASK of GT_CUSTOM_INST : label is "1111111000";
   attribute CRC_END_OF_PKT of GT_CUSTOM_INST : label is "K29_7";
   attribute CRC_FORMAT of GT_CUSTOM_INST : label is "USER_MODE";
   attribute CRC_START_OF_PKT of GT_CUSTOM_INST : label is "K27_7";
   attribute DEC_MCOMMA_DETECT of GT_CUSTOM_INST : label is "TRUE";
   attribute DEC_PCOMMA_DETECT of GT_CUSTOM_INST : label is "TRUE";
   attribute DEC_VALID_COMMA_ONLY of GT_CUSTOM_INST : label is "TRUE";
   attribute MCOMMA_10B_VALUE of GT_CUSTOM_INST : label is "1100000000";
   attribute MCOMMA_DETECT of GT_CUSTOM_INST : label is "TRUE";
   attribute PCOMMA_10B_VALUE of GT_CUSTOM_INST : label is "0011111000";
   attribute PCOMMA_DETECT of GT_CUSTOM_INST : label is "TRUE";
   attribute RX_BUFFER_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute RX_CRC_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute RX_DATA_WIDTH of GT_CUSTOM_INST : label is "4";
   attribute RX_DECODE_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute RX_LOSS_OF_SYNC_FSM of GT_CUSTOM_INST : label is "TRUE";
   attribute RX_LOS_INVALID_INCR of GT_CUSTOM_INST : label is "1";
   attribute RX_LOS_THRESHOLD of GT_CUSTOM_INST : label is "4";
   attribute TERMINATION_IMP of GT_CUSTOM_INST : label is "50";
   attribute SERDES_10B of GT_CUSTOM_INST : label is "FALSE";
   attribute TX_BUFFER_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute TX_CRC_FORCE_VALUE of GT_CUSTOM_INST : label is "11010110";
   attribute TX_CRC_USE of GT_CUSTOM_INST : label is "TRUE";
   attribute TX_DATA_WIDTH of GT_CUSTOM_INST : label is "4";
   attribute TX_DIFF_CTRL of GT_CUSTOM_INST : label is "500";
   attribute TX_PREEMPHASIS of GT_CUSTOM_INST : label is "0";
   attribute REF_CLK_V_SEL of GT_CUSTOM_INST : label is "0";
begin

   gnd(31 downto 0) <= X"00000000";
   gnd1 <= '0';
   pwr  <= '1';
   
   GT_CUSTOM_INST : GT_CUSTOM
   -- synopsys translate_off
   generic map( ALIGN_COMMA_MSB => TRUE,
            CHAN_BOND_LIMIT => 16,
            CHAN_BOND_MODE => "OFF",
            CHAN_BOND_OFFSET => 8,
            CHAN_BOND_ONE_SHOT => FALSE,
            CHAN_BOND_SEQ_1_1 => "00000000000",
            CHAN_BOND_SEQ_1_2 => "00000000000",
            CHAN_BOND_SEQ_1_3 => "00000000000",
            CHAN_BOND_SEQ_1_4 => "00000000000",
            CHAN_BOND_SEQ_2_1 => "00000000000",
            CHAN_BOND_SEQ_2_2 => "00000000000",
            CHAN_BOND_SEQ_2_3 => "00000000000",
            CHAN_BOND_SEQ_2_4 => "00000000000",
            CHAN_BOND_SEQ_2_USE => FALSE,
            CHAN_BOND_SEQ_LEN => 1,
            CHAN_BOND_WAIT => 8,
            CLK_CORRECT_USE => TRUE,
            CLK_COR_INSERT_IDLE_FLAG => TRUE,
            CLK_COR_KEEP_IDLE => FALSE,
            CLK_COR_REPEAT_WAIT => 1,
            CLK_COR_SEQ_1_1 => "00110111100",
            CLK_COR_SEQ_1_2 => "00001010000",
            CLK_COR_SEQ_1_3 => "00000000000",
            CLK_COR_SEQ_1_4 => "00000000000",
            CLK_COR_SEQ_2_1 => "00000000000",
            CLK_COR_SEQ_2_2 => "00000000000",
            CLK_COR_SEQ_2_3 => "00000000000",
            CLK_COR_SEQ_2_4 => "00000000000",
            CLK_COR_SEQ_2_USE => FALSE,
            CLK_COR_SEQ_LEN => 2,
            COMMA_10B_MASK => "1111111000",
            CRC_END_OF_PKT => "K29_7",
            CRC_FORMAT => "USER_MODE",
            CRC_START_OF_PKT => "K27_7",
            DEC_MCOMMA_DETECT => TRUE,
            DEC_PCOMMA_DETECT => TRUE,
            DEC_VALID_COMMA_ONLY => TRUE,
            MCOMMA_10B_VALUE => "1100000000",
            MCOMMA_DETECT => TRUE,
            PCOMMA_10B_VALUE => "0011111000",
            PCOMMA_DETECT => TRUE,
            RX_BUFFER_USE => TRUE,
            RX_CRC_USE => TRUE,
            RX_DATA_WIDTH => 4,
            RX_DECODE_USE => TRUE,
            RX_LOSS_OF_SYNC_FSM => TRUE,
            RX_LOS_INVALID_INCR => 1,
            RX_LOS_THRESHOLD => 4,
            TERMINATION_IMP => 50,
            SERDES_10B => FALSE,
            TX_BUFFER_USE => TRUE,
            TX_CRC_FORCE_VALUE => "11010110",
            TX_CRC_USE => TRUE,
            TX_DATA_WIDTH => 4,
            TX_DIFF_CTRL => 500,
            TX_PREEMPHASIS => 0,
            REF_CLK_V_SEL => 0)
   -- synopsys translate_on
      port map (BREFCLK=>gnd1,
                BREFCLK2=>gnd1,
                CHBONDI(3 downto 0)=>gnd(3 downto 0),
                CONFIGENABLE=>gnd1,
                CONFIGIN=>gnd1,
                ENCHANSYNC=>gnd1,
                ENMCOMMAALIGN=>gnd1,
                ENPCOMMAALIGN=>gnd1,
                LOOPBACK(1 downto 0)=>gnd(1 downto 0),
                POWERDOWN=>pwr,                             -- !POWERDOWN mode enabled!
                REFCLK=>gnd1,
                REFCLKSEL=>gnd1,
                REFCLK2=>gnd1,
                RXN=>RXN,
                RXP=>RXP,
                RXPOLARITY=>gnd1,
                RXRESET=>gnd1,
                RXUSRCLK=>gnd1,
                RXUSRCLK2=>gnd1,
                TXBYPASS8B10B(3 downto 0)=>gnd(3 downto 0),
                TXCHARDISPMODE(3 downto 0)=>gnd(3 downto 0),
                TXCHARDISPVAL(3 downto 0)=>gnd(3 downto 0),
                TXCHARISK(3 downto 0)=>gnd(3 downto 0),
                TXDATA(31 downto 0)=>gnd(31 downto 0),
                TXFORCECRCERR=>gnd1,
                TXINHIBIT=>gnd1,
                TXPOLARITY=>gnd1,
                TXRESET=>gnd1,
                TXUSRCLK=>gnd1,
                TXUSRCLK2=>gnd1,
                CHBONDDONE=>open,
                CHBONDO=>open,
                CONFIGOUT=>open,
                RXBUFSTATUS=>open,
                RXCHARISCOMMA=>open,
                RXCHARISK=>open,
                RXCHECKINGCRC=>open,
                RXCLKCORCNT=>open,
                RXCOMMADET=>open,
                RXCRCERR=>open,
                RXDATA=>open,
                RXDISPERR=>open,
                RXLOSSOFSYNC=>open,
                RXNOTINTABLE=>open,
                RXREALIGN=>open,
                RXRECCLK=>open,
                RXRUNDISP=>open,
                TXBUFERR=>open,
                TXKERR=>open,
                TXN=>TXN,
                TXP=>TXP,
                TXRUNDISP=>open
   );
end BEHAVIORAL;

