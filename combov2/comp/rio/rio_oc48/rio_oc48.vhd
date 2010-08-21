-- rio_oc48.vhd: RocketIO transceiver module for SONET/SDH (OC48)
-- Copyright (C) 2006 CESNET
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
--
library ieee;
use ieee.std_logic_1164.ALL;
use ieee.numeric_std.ALL;
-- synopsys translate_off
library UNISIM;
use UNISIM.Vcomponents.ALL;
-- synopsys translate_on

entity rio_oc48 is
   port ( 
      RESET             : in  std_logic;    
      -- Clocks
      BREFCLKNIN_IN     : in  std_logic; 
      BREFCLKPIN_IN     : in  std_logic; 
      USRCLK_IN         : in  std_logic; 
      USRCLK2_IN        : in  std_logic;       
      TXOUTCLK_OUT      : out std_logic;
      RXRECCLK_OUT      : out std_logic;       
      -- TX data     
      TXDATA_IN         : in  std_logic_vector (19 downto 0); 
      -- RX data 
      RXDATA_OUT        : out std_logic_vector (19 downto 0);       
      RXCHARISCOMMA_OUT : out std_logic_vector (1 downto 0); 
      RXCOMMADET_OUT    : out std_logic; 
      -- RIO serial data pads
      TXP_OUT           : out std_logic; 
      TXN_OUT           : out std_logic;       
      RXP_IN            : in  std_logic;       
      RXN_IN            : in  std_logic; 
      -- Control & status
      RXPOLARITY_IN     : in  std_logic; 
      TXPOLARITY_IN     : in  std_logic;
      RXLOSSOFSYNC_OUT  : out std_logic_vector (1 downto 0);       
      PMARXLOCK_OUT     : out std_logic;
      LOOPBACK_IN       : in  std_logic_vector (1 downto 0); 
      TXRUNDISP_OUT     : out std_logic_vector (1 downto 0)
   );
end rio_oc48;

architecture behavioral of rio_oc48 is

   attribute COMMA_10B_MASK      : string ;
   attribute PMA_SPEED           : string ;
   attribute ALIGN_COMMA_WORD    : string ;
   attribute DEC_MCOMMA_DETECT   : string ;
   attribute DEC_PCOMMA_DETECT   : string ;
   attribute MCOMMA_10B_VALUE    : string ;
   attribute MCOMMA_DETECT       : string ;
   attribute PCOMMA_10B_VALUE    : string ;
   attribute PCOMMA_DETECT       : string ;
   attribute PMA_PWR_CNTRL       : string ;
   attribute PMA_SPEED_HEX       : string ;
   attribute PMA_SPEED_USE       : string ;
   attribute RX_BUFFER_USE       : string ;
   attribute RX_LOS_INVALID_INCR : string ;
   attribute RX_LOS_THRESHOLD    : string ;
   attribute RX_LOSS_OF_SYNC_FSM : string ;
   attribute TX_BUFFER_USE       : string ;
   signal GND               : std_logic_vector (4 downto 0);
   signal GND1              : std_logic;
   signal GND2              : std_logic_vector (5 downto 0);
   signal GND3              : std_logic_vector (7 downto 0);
   signal GND4              : std_logic_vector (1 downto 0);
   signal VCC               : std_logic;
   signal VCC1              : std_logic_vector (1 downto 0);
   
   component GT10_OC48_2
   -- synopsys translate_off
   generic ( 
      ALIGN_COMMA_WORD : integer :=  1;
      DEC_MCOMMA_DETECT : boolean :=  TRUE;
      DEC_PCOMMA_DETECT : boolean :=  TRUE;
      MCOMMA_10B_VALUE : bit_vector :=  "0010101010";
      MCOMMA_DETECT : boolean :=  TRUE;
      PCOMMA_10B_VALUE : bit_vector :=  "0010101010";
      PCOMMA_DETECT : boolean :=  TRUE;
      PMA_PWR_CNTRL : bit_vector :=  "11111111";
      PMA_SPEED_HEX : bit_vector :=  x"00fc0d300b0f304830680901050820";
      PMA_SPEED_USE : string :=  "PMA_SPEED";
      RX_BUFFER_USE : boolean :=  TRUE;
      RX_LOS_INVALID_INCR : integer :=  1;
      RX_LOS_THRESHOLD : integer :=  4;
      RX_LOSS_OF_SYNC_FSM : boolean :=  TRUE;
      TX_BUFFER_USE : boolean :=  TRUE);
   -- synopsys translate_on
   port ( 
      BREFCLKNIN           : in    std_logic; 
      BREFCLKPIN           : in    std_logic; 
      CHBONDI              : in    std_logic_vector (4 downto 0); 
      ENCHANSYNC           : in    std_logic; 
      ENMCOMMAALIGN        : in    std_logic; 
      ENPCOMMAALIGN        : in    std_logic; 
      LOOPBACK             : in    std_logic_vector (1 downto 0); 
      PMAINIT              : in    std_logic; 
      PMAREGADDR           : in    std_logic_vector (5 downto 0); 
      PMAREGDATAIN         : in    std_logic_vector (7 downto 0); 
      PMAREGRW             : in    std_logic; 
      PMAREGSTROBE         : in    std_logic; 
      PMARXLOCKSEL         : in    std_logic_vector (1 downto 0); 
      POWERDOWN            : in    std_logic; 
      REFCLK               : in    std_logic; 
      REFCLK2              : in    std_logic; 
      REFCLKBSEL           : in    std_logic; 
      REFCLKSEL            : in    std_logic; 
      RXBLOCKSYNC64B66BUSE : in    std_logic; 
      RXCOMMADETUSE        : in    std_logic; 
      RXDATAWIDTH          : in    std_logic_vector (1 downto 0); 
      RXDEC64B66BUSE       : in    std_logic; 
      RXDEC8B10BUSE        : in    std_logic; 
      RXDESCRAM64B66BUSE   : in    std_logic; 
      RXIGNOREBTF          : in    std_logic; 
      RXINTDATAWIDTH       : in    std_logic_vector (1 downto 0); 
      RXN                  : in    std_logic; 
      RXP                  : in    std_logic; 
      RXPOLARITY           : in    std_logic; 
      RXRESET              : in    std_logic; 
      RXSLIDE              : in    std_logic; 
      RXUSRCLK             : in    std_logic; 
      RXUSRCLK2            : in    std_logic; 
      TXBYPASS8B10B        : in    std_logic_vector (1 downto 0); 
      TXCHARDISPMODE       : in    std_logic_vector (1 downto 0); 
      TXCHARDISPVAL        : in    std_logic_vector (1 downto 0); 
      TXCHARISK            : in    std_logic_vector (1 downto 0); 
      TXDATA               : in    std_logic_vector (15 downto 0); 
      TXDATAWIDTH          : in    std_logic_vector (1 downto 0); 
      TXENC64B66BUSE       : in    std_logic; 
      TXENC8B10BUSE        : in    std_logic; 
      TXGEARBOX64B66BUSE   : in    std_logic; 
      TXINHIBIT            : in    std_logic; 
      TXINTDATAWIDTH       : in    std_logic_vector (1 downto 0); 
      TXPOLARITY           : in    std_logic; 
      TXRESET              : in    std_logic; 
      TXSCRAM64B66BUSE     : in    std_logic; 
      TXUSRCLK             : in    std_logic; 
      TXUSRCLK2            : in    std_logic; 
      CHBONDDONE           : out   std_logic; 
      CHBONDO              : out   std_logic_vector (4 downto 0); 
      PMARXLOCK            : out   std_logic; 
      RXBUFSTATUS          : out   std_logic_vector (1 downto 0); 
      RXCHARISCOMMA        : out   std_logic_vector (1 downto 0); 
      RXCHARISK            : out   std_logic_vector (1 downto 0); 
      RXCLKCORCNT          : out   std_logic_vector (2 downto 0); 
      RXCOMMADET           : out   std_logic; 
      RXDATA               : out   std_logic_vector (15 downto 0); 
      RXDISPERR            : out   std_logic_vector (1 downto 0); 
      RXLOSSOFSYNC         : out   std_logic_vector (1 downto 0); 
      RXNOTINTABLE         : out   std_logic_vector (1 downto 0); 
      RXREALIGN            : out   std_logic; 
      RXRECCLK             : out   std_logic; 
      RXRUNDISP            : out   std_logic_vector (1 downto 0); 
      TXBUFERR             : out   std_logic; 
      TXKERR               : out   std_logic_vector (1 downto 0); 
      TXN                  : out   std_logic; 
      TXOUTCLK             : out   std_logic; 
      TXP                  : out   std_logic; 
      TXRUNDISP            : out   std_logic_vector (1 downto 0)
   );
   end component;
   
   attribute COMMA_10B_MASK of GT10_OC48_2          : component is "0011111111";
   attribute PMA_SPEED of GT10_OC48_2               : component is "30_16";
   attribute ALIGN_COMMA_WORD of GT10_OC48_2_INST   : label is "1";
   attribute DEC_MCOMMA_DETECT of GT10_OC48_2_INST  : label is "TRUE";
   attribute DEC_PCOMMA_DETECT of GT10_OC48_2_INST  : label is "TRUE";
   attribute MCOMMA_10B_VALUE of GT10_OC48_2_INST   : label is "0010101010";
   attribute MCOMMA_DETECT of GT10_OC48_2_INST      : label is "TRUE";
   attribute PCOMMA_10B_VALUE of GT10_OC48_2_INST   : label is "0010101010";
   attribute PCOMMA_DETECT of GT10_OC48_2_INST      : label is "TRUE";
   attribute PMA_PWR_CNTRL of GT10_OC48_2_INST      : label is "11111111";
   attribute PMA_SPEED_HEX of GT10_OC48_2_INST      : label is 
                                           "00fc0d300b0f304830680901050820";
   attribute PMA_SPEED_USE of GT10_OC48_2_INST      : label is "PMA_SPEED";
   attribute RX_BUFFER_USE of GT10_OC48_2_INST      : label is "TRUE";
   attribute RX_LOS_INVALID_INCR of GT10_OC48_2_INST: label is "1";
   attribute RX_LOS_THRESHOLD of GT10_OC48_2_INST   : label is "4";
   attribute RX_LOSS_OF_SYNC_FSM of GT10_OC48_2_INST: label is "TRUE";
   attribute TX_BUFFER_USE of GT10_OC48_2_INST      : label is "TRUE";
   
begin

   GND(4 downto 0) <= "00000";
   GND1 <= '0';
   GND2(5 downto 0) <= "000000";
   GND3(7 downto 0) <= "00000000";
   GND4(1 downto 0) <= "00";
   VCC <= '1';
   VCC1(1 downto 0) <= "11";
   
   GT10_OC48_2_INST : GT10_OC48_2
   -- synopsys translate_off
   generic map ( 
      ALIGN_COMMA_WORD    => 1,
      DEC_MCOMMA_DETECT   => TRUE,
      DEC_PCOMMA_DETECT   => TRUE,
      MCOMMA_10B_VALUE    => "0010101010",
      MCOMMA_DETECT       => TRUE,
      PCOMMA_10B_VALUE    => "0010101010",
      PCOMMA_DETECT       => TRUE,
      PMA_PWR_CNTRL       => "11111111",
      PMA_SPEED_HEX       => x"00fc0d300b0f304830680901050820",
      PMA_SPEED_USE       => "PMA_SPEED",
      RX_BUFFER_USE       => TRUE,
      RX_LOS_INVALID_INCR => 1,
      RX_LOS_THRESHOLD    => 4,
      RX_LOSS_OF_SYNC_FSM => TRUE,
      TX_BUFFER_USE       => TRUE)
   -- synopsys translate_on
   port map (
      -- Clocking 
      BREFCLKNIN               => BREFCLKNIN_IN,
      BREFCLKPIN               => BREFCLKPIN_IN,
      REFCLK                   => GND1,
      REFCLKBSEL               => VCC,
      REFCLKSEL                => GND1,
      REFCLK2                  => GND1,
      --      
      CHBONDI(4 downto 0)      => GND(4 downto 0),
      ENCHANSYNC               => GND1,
      ENMCOMMAALIGN            => VCC,
      ENPCOMMAALIGN            => VCC,
      LOOPBACK(1 downto 0)     => LOOPBACK_IN(1 downto 0),
      PMAINIT                  => GND1,
      PMAREGADDR(5 downto 0)   => GND2(5 downto 0),
      PMAREGDATAIN(7 downto 0) => GND3(7 downto 0),
      PMAREGRW                 => GND1,
      PMAREGSTROBE             => GND1,
      PMARXLOCKSEL(1 downto 0) => GND4,
      POWERDOWN                => GND1,
      -- RX
      RXBLOCKSYNC64B66BUSE     => GND1,
      RXCOMMADETUSE            => VCC,
      RXDATAWIDTH(1 downto 0)  => "01",     -- Set 16/20bit data bus widt
      RXDEC8B10BUSE            => GND1,
      RXDEC64B66BUSE           => GND1,
      RXDESCRAM64B66BUSE       => GND1,
      RXIGNOREBTF              => GND1,
      RXINTDATAWIDTH(1 downto 0)=>GND4,    -- Set 16bit internal bus width
      RXN                      => RXN_IN,
      RXP                      => RXP_IN,
      RXPOLARITY               => RXPOLARITY_IN,
      RXRESET                  => RESET,
      RXSLIDE                  => GND1,
      RXUSRCLK                 => USRCLK_IN,
      RXUSRCLK2                => USRCLK2_IN,
      TXBYPASS8B10B(1 downto 0)=> VCC1(1 downto 0),
      -- TX
      TXCHARDISPMODE(1)        => TXDATA_IN(19),
      TXCHARDISPMODE(0)        => TXDATA_IN(9),
      TXCHARDISPVAL(1)         => TXDATA_IN(18),
      TXCHARDISPVAL(0)         => TXDATA_IN(8),
      TXDATA(15 downto 8)      => TXDATA_IN(17 downto 10),
      TXDATA(7 downto 0)       => TXDATA_IN(7 downto 0),      
      TXCHARISK(1 downto 0)    => GND4(1 downto 0),
      TXDATAWIDTH(1 downto 0)  => "01",     -- Set 16/20bit data bus widt
      TXENC8B10BUSE            => GND1,
      TXENC64B66BUSE           => GND1,
      TXGEARBOX64B66BUSE       => GND1,
      TXINHIBIT                => GND1,
      TXINTDATAWIDTH(1 downto 0)=>GND4,    -- Set 16bit internal bus width
      TXPOLARITY               => TXPOLARITY_IN,
      TXRESET                  => RESET,
      TXSCRAM64B66BUSE         => GND1,
      TXUSRCLK                 => USRCLK_IN,
      TXUSRCLK2                => USRCLK2_IN,
      CHBONDDONE               => open,
      CHBONDO                  => open,
      PMARXLOCK                => PMARXLOCK_OUT,
      RXBUFSTATUS(1 downto 0)  => open,
      RXCHARISCOMMA(1 downto 0)=> RXCHARISCOMMA_OUT(1 downto 0),
      RXCHARISK(1)             => RXDATA_OUT(19),
      RXCHARISK(0)             => RXDATA_OUT(9),
      RXCLKCORCNT(2 downto 0)  => open,
      RXCOMMADET               => RXCOMMADET_OUT,
      RXDATA(15 downto 8)      => RXDATA_OUT(17 downto 10),
      RXDATA(7 downto 0)       => RXDATA_OUT(7 downto 0),
      RXDISPERR                => open,
      RXLOSSOFSYNC(1 downto 0) => RXLOSSOFSYNC_OUT(1 downto 0),
      RXNOTINTABLE             => open,
      RXREALIGN                => open,
      RXRECCLK                 => RXRECCLK_OUT,
      RXRUNDISP(1)             => RXDATA_OUT(18),
      RXRUNDISP(0)             => RXDATA_OUT(8),
      TXBUFERR                 => open,
      TXKERR                   => open,
      TXN                      => TXN_OUT,
      TXP                      => TXP_OUT,                
      TXOUTCLK                 => TXOUTCLK_OUT,
      TXRUNDISP(1 downto 0)    => TXRUNDISP_OUT(1 downto 0)
   );
   
end behavioral;


