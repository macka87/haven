--   clk2x.vhd : Twice multiply clock generation  
--   Copyright (C) 2003 CESNET
--   Author(s): Jan Korenek <korenek@liberouter.org>
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
-- TODO list :  
--
--
--

library IEEE;
use IEEE.std_logic_1164.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

-- ------------------------------------------------------------------------
--         Entity : BUFG_CLK2X_SUBM 
-- ------------------------------------------------------------------------

entity CLK2X_MOD is
   port ( 
      CLK_IN   : in std_logic;
      RST      : in std_logic;
      CLK1X    : out std_logic;
      CLK1X_PH : out std_logic;
      CLK2X    : out std_logic;
      CLK2X_PH : out std_logic;
      CLK2DV   : out std_logic;
      CLK2DV_PH: out std_logic;
      LOCK     : out std_logic
   );
end clk2x_mod;

-- ------------------------------------------------------------------------
--         Architecture : BUFG_CLK2X_SUBM_arch 
-- ------------------------------------------------------------------------

architecture behavioral of clk2x_mod is

-- Components Declarations:
component BUFG 
   port (
      I   : in std_logic;
      O   : out std_logic
   ); 
end component;

component DCM
   -- pragma translate_off
   generic ( 
      DLL_FREQUENCY_MODE : string := "LOW";
      DUTY_CYCLE_CORRECTION : boolean := TRUE;
      STARTUP_WAIT : boolean := FALSE;
      CLKDV_DIVIDE : real := 2.0
   );  
   -- pragma translate_on

   port ( 
      CLKIN     : in  std_logic;
      CLKFB     : in  std_logic;
      DSSEN     : in  std_logic;
      PSINCDEC  : in  std_logic;
      PSEN      : in  std_logic;
      PSCLK     : in  std_logic;
      RST       : in  std_logic;
      CLK0      : out std_logic;
      CLK90     : out std_logic;
      CLK180    : out std_logic;
      CLK270    : out std_logic;
      CLK2X     : out std_logic;
      CLK2X180  : out std_logic;
      CLKDV     : out std_logic;
      CLKFX     : out std_logic;
      CLKFX180  : out std_logic;
      LOCKED    : out std_logic;
      PSDONE    : out std_logic;
      STATUS    : out std_logic_vector(7 downto 0)
   );
end component;


-- Attributes
attribute DLL_FREQUENCY_MODE     : string; 
attribute DUTY_CYCLE_CORRECTION  : string; 
attribute STARTUP_WAIT           : string; 
attribute CLKDV_DIVIDE           : real; 

attribute DLL_FREQUENCY_MODE of U_DCM: label is "LOW";
attribute DUTY_CYCLE_CORRECTION of U_DCM: label is "TRUE";
attribute STARTUP_WAIT of U_DCM: label is "FALSE";
attribute CLKDV_DIVIDE of U_DCM: label is 2.0;

attribute DLL_FREQUENCY_MODE of U_DCMDV: label is "LOW";
attribute DUTY_CYCLE_CORRECTION of U_DCMDV: label is "TRUE";
attribute STARTUP_WAIT of U_DCMDV: label is "FALSE";
attribute CLKDV_DIVIDE of U_DCMDV: label is 2.0;


-- -----------------------------------------------------------------------
-- Signal Declarations:
signal gnd           : std_logic;
signal clk2_w        : std_logic;
signal clk2_ph180_w  : std_logic;     -- shifted 2x clock (180' phase)
signal clk1_w        : std_logic;
signal clk1_ph_w     : std_logic;     -- shifted basic clock
signal clk1x_fb      : std_logic;

-- Clock inteconnect signals 
signal clkdv_w     : std_logic;
signal clkdv_buf   : std_logic;
signal clkdvin_w   : std_logic;
signal clkdvin_buf : std_logic;
signal clkdvph_w   : std_logic;
signal clkdvph_buf : std_logic;
signal lock1       : std_logic;
signal lockdv      : std_logic;

signal reg1_dcm1rst     : std_logic;
signal reg2_dcm1rst     : std_logic;
signal reg3_dcm1rst     : std_logic;


begin
gnd   <= '0';
CLK1X <= clk1x_fb;

-- DCM Instantiation
U_DCM: DCM
   -- pragma translate_off
   generic map ( 
      DLL_FREQUENCY_MODE =>  "LOW", 
      DUTY_CYCLE_CORRECTION => TRUE,
      STARTUP_WAIT =>  FALSE,
      CLKDV_DIVIDE => 2.0
   ) 
   -- pragma translate_on
   port map (
      CLKIN =>    CLK_IN,
      CLKFB =>    clk1x_fb,
      DSSEN =>    gnd,
      PSINCDEC => gnd,
      PSEN =>     gnd,
      PSCLK =>    gnd,
      RST =>      RST,
      CLK0 =>     clk1_w,
      CLK90=>     clk1_ph_w,
      CLK2X =>    clk2_w,
      CLK2X180 => clk2_ph180_w,
      CLKDV  =>   clkdvin_w,
      LOCKED =>   lock1 
   ); 


-- reg_dcmrst register
process(RST, clkdvin_buf)
begin
   if (RST = '1') then
      reg1_dcm1rst <= '1';
      reg2_dcm1rst <= '1';
      reg3_dcm1rst <= '1';
   elsif (clkdvin_buf'event AND clkdvin_buf = '1') then
         reg1_dcm1rst <= not lock1;
         reg2_dcm1rst <= reg1_dcm1rst;
         reg3_dcm1rst <= reg2_dcm1rst;
   end if;
end process;


-- BUFG Instantiation
BUFG2X_U : BUFG
   port map (
      I => clk2_w,
      O => CLK2X
   );

-- BUFG Instantiation
BUFG2XPH180_U : BUFG
   port map (
      I => clk2_ph180_w,
      O => CLK2X_PH
   );

-- BUFG Instantiation
BUFG1X_U : BUFG
   port map (
      I => clk1_w,
      O => clk1x_fb
   );

-- BUFG Instantiation
BUFG1XPH_U : BUFG
   port map (
      I => clk1_ph_w,
      O => CLK1X_PH 
   );


-- BUFG Instantiation
BUFDV_IN_U : BUFG
   port map (
      I => clkdvin_w,
      O => clkdvin_buf
   );

-- ---------------- DV frequency ------------------
-- DCM Instantiation
U_DCMDV: DCM
   -- pragma translate_off
   generic map ( 
      DLL_FREQUENCY_MODE =>  "LOW", 
      DUTY_CYCLE_CORRECTION => TRUE,
      STARTUP_WAIT =>  FALSE,
      CLKDV_DIVIDE => 2.0
   )  
   -- pragma translate_on
   port map (
      CLKIN =>    clkdvin_buf,
      CLKFB =>    clkdv_buf,
      DSSEN =>    gnd,
      PSINCDEC => gnd,
      PSEN =>     gnd,
      PSCLK =>    gnd,
      RST =>      reg3_dcm1rst,
      CLK0 =>     clkdv_w,
      CLK90=>     clkdvph_w,
      LOCKED =>   lockdv 
   ); 

-- BUFG Instantiation
BUFDV_U : BUFG
   port map (
      I => clkdv_w,
      O => clkdv_buf
   );

-- BUFG Instantiation
BUFDV_PHU : BUFG
   port map (
      I => clkdvph_w,
      O => clkdvph_buf
   );

CLK2DV      <=  clkdv_buf;
CLK2DV_PH   <=  clkdvph_buf;
LOCK        <=  lock1 and lockdv;

end behavioral;
