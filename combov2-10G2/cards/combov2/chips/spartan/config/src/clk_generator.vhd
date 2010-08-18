--
-- clk_generator.vhd: Clock generator for FPGA config design (sp3e -> virtex5)
-- Copyright (C) 2008  CESNET
-- Author: Milan Malich <malich@mail.muni.cz>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
library UNISIM;
use UNISIM.VComponents.all;

entity clk_generator is
    Generic (
      CLK_DIVIDE : integer := 1;
      CLK_MULTIPLY : integer := 1
    );
    Port (
      CLK_I : in  std_logic;
      RST_I : in  std_logic;
      --
      CLK_O : out  std_logic;
      LOCKED_O : out std_logic
    );
end clk_generator;

architecture Behavioral of clk_generator is

  signal rst : std_logic;
  signal locked : std_logic;
  signal clk_input : std_logic;
  signal clk_input_bufg : std_logic;
  signal clk_output : std_logic;
  signal clk_output_bufg : std_logic;
  signal clk0_output : std_logic;
  signal clk0_output_bufg : std_logic;
begin
    
    -- Map signal
    clk_input <= CLK_I;
    rst <= RST_I;
    LOCKED_O <= locked;
    CLK_O <= clk_output_bufg;
    --

    INST_IBUFG : IBUFG
    generic map (
      IOSTANDARD => "DEFAULT")
    port map (
      O => clk_input_bufg, -- Clock buffer output
      I => clk_input  -- Clock buffer input (connect directly to top-level port)
    );
   
    INST_BUFG : BUFG
    port map (
      O => clk_output_bufg,     -- Clock buffer output
      I => clk_output      -- Clock buffer input
    );
    
    INST_FEEDBACK_BUFG : BUFG
    port map (
      O => clk0_output_bufg,     -- Clock buffer output
      I => clk0_output      -- Clock buffer input
    );
   
   -- DCM_SP: Digital Clock Manager Circuit
   --         Spartan-3E/3A
   -- Xilinx HDL Language Template, version 10.1.2
   INST_DCM_SP : DCM_SP
   generic map (
      CLKDV_DIVIDE => 2.0, --  Divide by: 1.5,2.0,2.5,3.0,3.5,4.0,4.5,5.0,5.5,6.0,6.5
                           --     7.0,7.5,8.0,9.0,10.0,11.0,12.0,13.0,14.0,15.0 or 16.0
      CLKFX_DIVIDE => CLK_DIVIDE,   --  Can be any interger from 1 to 32
      CLKFX_MULTIPLY => CLK_MULTIPLY, --  Can be any integer from 1 to 32
      CLKIN_DIVIDE_BY_2 => FALSE, --  TRUE/FALSE to enable CLKIN divide by two feature
      CLKIN_PERIOD => 10000.0, --  Specify period of input clock
      CLKOUT_PHASE_SHIFT => "NONE", --  Specify phase shift of "NONE", "FIXED" or "VARIABLE" 
      CLK_FEEDBACK => "1X",         --  Specify clock feedback of "NONE", "1X" or "2X" 
      DESKEW_ADJUST => "SYSTEM_SYNCHRONOUS", -- "SOURCE_SYNCHRONOUS", "SYSTEM_SYNCHRONOUS" or
                                             --     an integer from 0 to 15
      DLL_FREQUENCY_MODE => "LOW",     -- "HIGH" or "LOW" frequency mode for DLL
      DUTY_CYCLE_CORRECTION => TRUE, --  Duty cycle correction, TRUE or FALSE
      PHASE_SHIFT => 0,        --  Amount of fixed phase shift from -255 to 255
      STARTUP_WAIT => FALSE) --  Delay configuration DONE until DCM_SP LOCK, TRUE/FALSE
   port map (
      CLK0 => clk0_output,     -- 0 degree DCM CLK ouptput
      CLK180 => open, -- 180 degree DCM CLK output
      CLK270 => open, -- 270 degree DCM CLK output
      CLK2X => open,   -- 2X DCM CLK output
      CLK2X180 => open, -- 2X, 180 degree DCM CLK out
      CLK90 => open,   -- 90 degree DCM CLK output
      CLKDV => open,   -- Divided DCM CLK out (CLKDV_DIVIDE)
      CLKFX => clk_output,   -- DCM CLK synthesis out (M/D)
      CLKFX180 => open, -- 180 degree CLK synthesis out
      LOCKED => LOCKED, -- DCM LOCK status output
      PSDONE => open, -- Dynamic phase adjust done output
      STATUS => open, -- 8-bit DCM status bits output
      CLKFB => clk0_output_bufg,   -- DCM clock feedback
      CLKIN => clk_input_bufg,   -- Clock input (from IBUFG, BUFG or DCM)
      PSCLK => '0',   -- Dynamic phase adjust clock input
      PSEN => '0',     -- Dynamic phase adjust enable input
      PSINCDEC => '0', -- Dynamic phase adjust increment/decrement
      RST => rst        -- DCM asynchronous reset input
   );

end Behavioral;

