--
-- clk200gen.vhd : Clock generator for the QDRII memory test
-- Copyright (C) 2008 CESNET
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


library ieee;
use ieee.std_logic_1164.ALL;
use ieee.numeric_std.ALL;
library UNISIM;
use UNISIM.Vcomponents.ALL;

entity clk200gen is
   port ( CLKIN_IN        : in    std_logic; 
          RST_IN          : in    std_logic; 
          CLKFX_OUT       : out   std_logic; 
          CLK0_OUT        : out   std_logic; 
          CLK2X_OUT       : out   std_logic; 
          CLK180_OUT      : out   std_logic; 
          CLK270_OUT      : out   std_logic; 
          LOCKED_OUT      : out   std_logic);
end clk200gen;

architecture behavioral of clk200gen is

attribute CLK_FEEDBACK          : string ;
attribute CLKDV_DIVIDE          : string ;
attribute CLKFX_DIVIDE          : string ;
attribute CLKFX_MULTIPLY        : string ;
attribute CLKIN_DIVIDE_BY_2     : string ;
attribute CLKIN_PERIOD          : string ;
attribute CLKOUT_PHASE_SHIFT    : string ;
attribute DCM_AUTOCALIBRATION   : string ;
attribute DCM_PERFORMANCE_MODE  : string ;
attribute DESKEW_ADJUST         : string ;
attribute DFS_FREQUENCY_MODE    : string ;
attribute DLL_FREQUENCY_MODE    : string ;
attribute DUTY_CYCLE_CORRECTION : string ;
attribute FACTORY_JF            : string ;
attribute PHASE_SHIFT           : string ;
attribute STARTUP_WAIT          : string ;
attribute SIM_DEVICE            : string ;

component BUFG
   port ( I : in    std_logic; 
          O : out   std_logic);
end component;

component IBUFG
   port ( I : in    std_logic; 
          O : out   std_logic);
end component;

component DCM_ADV
   -- synopsys translate_off
   generic( CLK_FEEDBACK : string :=  "1X";
            CLKDV_DIVIDE : real :=  2.0;
            CLKFX_DIVIDE : integer :=  1;
            CLKFX_MULTIPLY : integer :=  4;
            CLKIN_DIVIDE_BY_2 : boolean :=  FALSE;
            CLKIN_PERIOD : real :=  10.0;
            CLKOUT_PHASE_SHIFT : string :=  "NONE";
            DCM_AUTOCALIBRATION : boolean :=  TRUE;
            DCM_PERFORMANCE_MODE : string :=  "MAX_SPEED";
            DESKEW_ADJUST : string :=  "SYSTEM_SYNCHRONOUS";
            DFS_FREQUENCY_MODE : string :=  "LOW";
            DLL_FREQUENCY_MODE : string :=  "LOW";
            DUTY_CYCLE_CORRECTION : boolean :=  TRUE;
            FACTORY_JF : bit_vector :=  x"F0F0";
            PHASE_SHIFT : integer :=  0;
            STARTUP_WAIT : boolean :=  FALSE;
            SIM_DEVICE : string :=  "VIRTEX4");
   -- synopsys translate_on
   port ( CLKIN    : in    std_logic; 
          CLKFB    : in    std_logic; 
          DADDR    : in    std_logic_vector (6 downto 0); 
          DI       : in    std_logic_vector (15 downto 0); 
          DWE      : in    std_logic; 
          DEN      : in    std_logic; 
          DCLK     : in    std_logic; 
          RST      : in    std_logic; 
          PSEN     : in    std_logic; 
          PSINCDEC : in    std_logic; 
          PSCLK    : in    std_logic; 
          CLK0     : out   std_logic; 
          CLK90    : out   std_logic; 
          CLK180   : out   std_logic; 
          CLK270   : out   std_logic; 
          CLKDV    : out   std_logic; 
          CLK2X    : out   std_logic; 
          CLK2X180 : out   std_logic; 
          CLKFX    : out   std_logic; 
          CLKFX180 : out   std_logic; 
          DRDY     : out   std_logic; 
          DO       : out   std_logic_vector (15 downto 0); 
          LOCKED   : out   std_logic; 
          PSDONE   : out   std_logic);
end component;

attribute CLK_FEEDBACK of DCM_ADV_INST : label is "1X";
attribute CLKDV_DIVIDE of DCM_ADV_INST : label is "2.0";
attribute CLKFX_DIVIDE of DCM_ADV_INST : label is "5";
attribute CLKFX_MULTIPLY of DCM_ADV_INST : label is "8";
attribute CLKIN_DIVIDE_BY_2 of DCM_ADV_INST : label is "FALSE";
attribute CLKIN_PERIOD of DCM_ADV_INST : label is "8.000";
attribute CLKOUT_PHASE_SHIFT of DCM_ADV_INST : label is "NONE";
attribute DCM_AUTOCALIBRATION of DCM_ADV_INST : label is "TRUE";
attribute DCM_PERFORMANCE_MODE of DCM_ADV_INST : label is "MAX_SPEED";
attribute DESKEW_ADJUST of DCM_ADV_INST : label is "SYSTEM_SYNCHRONOUS";
attribute DFS_FREQUENCY_MODE of DCM_ADV_INST : label is "HIGH";
attribute DLL_FREQUENCY_MODE of DCM_ADV_INST : label is "HIGH";
attribute DUTY_CYCLE_CORRECTION of DCM_ADV_INST : label is "TRUE";
attribute FACTORY_JF of DCM_ADV_INST : label is "F0F0";
attribute PHASE_SHIFT of DCM_ADV_INST : label is "0";
attribute STARTUP_WAIT of DCM_ADV_INST : label is "FALSE";
attribute SIM_DEVICE of DCM_ADV_INST : label is "VIRTEX5";

signal CLKFB_IN        : std_logic;
signal CLKFX_BUF       : std_logic;
signal CLK0_BUF        : std_logic;
signal CLK180_BUF      : std_logic;
signal CLK270_BUF      : std_logic;
signal CLK2X_BUF       : std_logic;
signal GND_BIT         : std_logic;
signal GND_BUS_7       : std_logic_vector (6 downto 0);
signal GND_BUS_16      : std_logic_vector (15 downto 0);

begin

   GND_BIT <= '0';
   GND_BUS_7(6 downto 0) <= "0000000";
   GND_BUS_16(15 downto 0) <= "0000000000000000";
   CLK0_OUT <= CLKFB_IN;
   CLKFX_BUFG_INST : BUFG
      port map (I=>CLKFX_BUF,
                O=>CLKFX_OUT);
 
   CLK0_BUFG_INST : BUFG
      port map (I=>CLK0_BUF,
                O=>CLKFB_IN);
   
   CLK180_BUFG_INST : BUFG
   port map (I=>CLK180_BUF,
             O=>CLK180_OUT);

   CLK270_BUFG_INST : BUFG
   port map (I=>CLK270_BUF,
             O=>CLK270_OUT);
             
   CLK2X_BUFG_INST : BUFG
      port map (I=>CLK2X_BUF,
                O=>CLK2X_OUT);             
                
   
   DCM_ADV_INST : DCM_ADV
   -- synopsys translate_off
   generic map( 
            CLK_FEEDBACK          => "1X",
            CLKDV_DIVIDE          => 2.0,
            CLKFX_DIVIDE          => 5,
            CLKFX_MULTIPLY        => 8,
            CLKIN_DIVIDE_BY_2     => FALSE,
            CLKIN_PERIOD          => 8.000,
            CLKOUT_PHASE_SHIFT    => "NONE",
            DCM_AUTOCALIBRATION   => TRUE,
            DCM_PERFORMANCE_MODE  => "MAX_SPEED",
            DESKEW_ADJUST         => "SYSTEM_SYNCHRONOUS",
            DFS_FREQUENCY_MODE    => "HIGH",
            DLL_FREQUENCY_MODE    => "HIGH",
            DUTY_CYCLE_CORRECTION => TRUE,
            FACTORY_JF            => x"F0F0",
            PHASE_SHIFT           => 0,
            STARTUP_WAIT          => FALSE,
            SIM_DEVICE            => "VIRTEX5")
   -- synopsys translate_on
      port map (CLKFB    => CLKFB_IN,
                CLKIN    => CLKIN_IN,
                DADDR(6 downto 0)=> GND_BUS_7(6 downto 0),
                DCLK     => GND_BIT,
                DEN      => GND_BIT,
                DI(15 downto 0)=> GND_BUS_16(15 downto 0),
                DWE      => GND_BIT,
                PSCLK    => GND_BIT,
                PSEN     => GND_BIT,
                PSINCDEC => GND_BIT,
                RST      => RST_IN,
                CLKDV    => open,
                CLKFX    => CLKFX_BUF,
                CLKFX180 => open,
                CLK0     => CLK0_BUF,
                CLK2X    => CLK2X_BUF,
                CLK2X180 => open,
                CLK90    => open,
                CLK180   => CLK180_BUF,
                CLK270   => CLK270_BUF,
                DO       => open,
                DRDY     => open,
                LOCKED   => LOCKED_OUT,
                PSDONE   => open
             );
   
end behavioral;
