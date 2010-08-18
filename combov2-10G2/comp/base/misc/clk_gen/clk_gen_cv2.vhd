-- clk_gen_cv2.vhd: Clock generation module for ComboV2
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
library unisim;
use UNISIM.vcomponents.all;
use work.clk_gen_pkg.all;

-- ----------------------------------------------------------------------
--         Entity : clk_gen
-- ----------------------------------------------------------------------
entity CLK_GEN_CV2 is
   generic(
      INPUT_IS_125   : boolean := false;  -- Default input freq is 250

      CLK_MULT       : integer := 16;  -- Multiply from 62.5 MHz, from 400 to 1000 MHz

      CLK_ICS_DIV    : integer := 8;   -- Derive from CLK_MULT
      CLK_USER0_DIV  : integer := 8;   -- Derive from CLK_MULT
      CLK_USER1_DIV  : integer := 8;   -- Derive from CLK_MULT
      CLK_USER2_DIV  : integer := 8;   -- Derive from CLK_MULT
      CLK_USER3_DIV  : integer := 8;   -- Derive from CLK_MULT
      CLK_USER4_DIV  : integer := 8    -- Derive from CLK_MULT
   );
   port(
      CLK_IN            : in  std_logic;  -- 250 (or 125) MHz input clock
      RESET             : in  std_logic;

      CLK62_5_OUT       : out std_logic;
      CLK100_OUT        : out std_logic;
      CLK125_OUT        : out std_logic;
      CLK250_OUT        : out std_logic;
      CLK200_OUT        : out std_logic;
      CLK166_OUT        : out std_logic;

      CLK_ICS_OUT       : out std_logic;
      CLK_USER0_OUT     : out std_logic;
      CLK_USER1_OUT     : out std_logic;
      CLK_USER2_OUT     : out std_logic;
      CLK_USER3_OUT     : out std_logic;
      CLK_USER4_OUT     : out std_logic;

      LOCK              : out std_logic
   );
end clk_gen_cv2;

architecture full of clk_gen_cv2 is

   constant clkin_per : real := cv2_clkper(INPUT_IS_125); -- Function from clk_gen_pkg, returns 4 or 8
   constant clkin_mult : integer := cv2_mult(INPUT_IS_125); -- Returns 2 

   signal pll0_clk0        : std_logic;
   signal pll0_clk0_buf    : std_logic;
   signal pll0_clk1        : std_logic;
   signal pll0_clk1_buf    : std_logic;
   signal pll0_clk2        : std_logic;
   signal pll0_clk2_buf    : std_logic;
   signal pll0_clk3        : std_logic;
   signal pll0_clk3_buf    : std_logic;
   signal pll0_clk4        : std_logic;
   signal pll0_clk4_buf    : std_logic;
   signal pll0_clk5        : std_logic;
   signal pll0_clk5_buf    : std_logic;

   signal pll0_locked      : std_logic;
   signal pll0_fb          : std_logic; -- Not used, Internal Feedback used

   signal pll1_clk0        : std_logic;
   signal pll1_clk0_buf    : std_logic;
   signal pll1_clk1        : std_logic;
   signal pll1_clk1_buf    : std_logic;
   signal pll1_clk2        : std_logic;
   signal pll1_clk2_buf    : std_logic;
   signal pll1_clk3        : std_logic;
   signal pll1_clk3_buf    : std_logic;
   signal pll1_clk4        : std_logic;
   signal pll1_clk4_buf    : std_logic;
   signal pll1_clk5        : std_logic;
   signal pll1_clk5_buf    : std_logic;

   signal pll1_locked      : std_logic;
   signal pll1_reset       : std_logic;
   signal pll1_fb          : std_logic; -- Not used, Internal Feedback used

begin

   -- First PLL: Create a set of fixed clocks.
   PLL_BASE_inst0 : PLL_BASE
   generic map (
      BANDWIDTH => "OPTIMIZED",  -- "HIGH", "LOW" or "OPTIMIZED" 
      CLKFBOUT_MULT => clkin_mult,-- Multiplication factor for all output clocks
      CLKFBOUT_PHASE => 0.0,     -- Phase shift (degrees) of all output clocks
      CLKIN_PERIOD => clkin_per, -- Clock period (ns) of input clock on CLKIN
      CLKOUT0_DIVIDE => 16,      -- Division factor for CLKOUT0  (1 to 128)
      CLKOUT0_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT0 (0.01 to 0.99)
      CLKOUT0_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT0 (0.0 to 360.0)
      CLKOUT1_DIVIDE => 10,      -- Division factor for CLKOUT1 (1 to 128)
      CLKOUT1_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT1 (0.01 to 0.99)
      CLKOUT1_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT1 (0.0 to 360.0)
      CLKOUT2_DIVIDE => 8,       -- Division factor for CLKOUT2 (1 to 128)
      CLKOUT2_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT2 (0.01 to 0.99)
      CLKOUT2_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT2 (0.0 to 360.0)
      CLKOUT3_DIVIDE => 4,       -- Division factor for CLKOUT3 (1 to 128)
      CLKOUT3_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT3 (0.01 to 0.99)
      CLKOUT3_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT3 (0.0 to 360.0)
      CLKOUT4_DIVIDE => 5,-- Division factor for CLKOUT4 (1 to 128)
      CLKOUT4_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT4 (0.01 to 0.99)
      CLKOUT4_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT4 (0.0 to 360.0)
      CLKOUT5_DIVIDE => 6,-- Division factor for CLKOUT5 (1 to 128)
      CLKOUT5_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT5 (0.01 to 0.99)
      CLKOUT5_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT5 (0.0 to 360.0)
      COMPENSATION => "INTERNAL",  -- "SYSTEM_SYNCHRNOUS", 
                                             -- "SOURCE_SYNCHRNOUS", "INTERNAL", 
                                             -- "EXTERNAL", "DCM2PLL", "PLL2DCM" 
      DIVCLK_DIVIDE => 1,      -- Division factor for all clocks (1 to 52)
      REF_JITTER => 0.100)     -- Input reference jitter (0.000 to 0.999 UI%)
   port map (
      CLKFBOUT => pll0_fb,      -- General output feedback signal
      CLKOUT0 => pll0_clk0,        -- One of six general clock output signals
      CLKOUT1 => pll0_clk1,        -- One of six general clock output signals
      CLKOUT2 => pll0_clk2,        -- One of six general clock output signals
      CLKOUT3 => pll0_clk3,        -- One of six general clock output signals
      CLKOUT4 => pll0_clk4,        -- One of six general clock output signals
      CLKOUT5 => pll0_clk5,        -- One of six general clock output signals
      LOCKED => pll0_locked,          -- Active high PLL lock signal
      CLKFBIN => pll0_fb,        -- Clock feedback input
      CLKIN => CLK_IN,           -- Clock input
      RST => RESET               -- Asynchronous PLL reset
   );

   -- Global clock buffers for clocks
   clk0_bufg_inst0 : BUFG
   port map(i => pll0_clk0,
            o => pll0_clk0_buf);
   clk1_bufg_inst0 : BUFG
   port map(i => pll0_clk1,
            o => pll0_clk1_buf);
   clk2_bufg_inst0 : BUFG
   port map(i => pll0_clk2,
            o => pll0_clk2_buf);
   clk3_bufg_inst0 : BUFG
   port map(i => pll0_clk3,
            o => pll0_clk3_buf);
   clk4_bufg_inst0 : BUFG
   port map(i => pll0_clk4,
            o => pll0_clk4_buf);
   clk5_bufg_inst0 : BUFG
   port map(i => pll0_clk5,
            o => pll0_clk5_buf);

   -- Port mapping of clock buffers outputs
   CLK62_5_OUT       <= pll0_clk0_buf;
   CLK100_OUT        <= pll0_clk1_buf;
   CLK125_OUT        <= pll0_clk2_buf;
   CLK250_OUT        <= pll0_clk3_buf;
   CLK200_OUT        <= pll0_clk4_buf;
   CLK166_OUT        <= pll0_clk5_buf;

   -- Second PLL: Create a set of variable clocks.
   PLL_BASE_inst1 : PLL_BASE
   generic map (
      BANDWIDTH => "OPTIMIZED",  -- "HIGH", "LOW" or "OPTIMIZED" 
      CLKFBOUT_MULT => CLK_MULT,-- Multiplication factor for all output clocks
      CLKFBOUT_PHASE => 0.0,     -- Phase shift (degrees) of all output clocks
      CLKIN_PERIOD => 16.0, -- Clock period (ns) of input clock on CLKIN
      CLKOUT0_DIVIDE => CLK_ICS_DIV,      -- Division factor for CLKOUT0  (1 to 128)
      CLKOUT0_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT0 (0.01 to 0.99)
      CLKOUT0_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT0 (0.0 to 360.0)
      CLKOUT1_DIVIDE => CLK_USER0_DIV,-- Division factor for CLKOUT1 (1 to 128)
      CLKOUT1_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT1 (0.01 to 0.99)
      CLKOUT1_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT1 (0.0 to 360.0)
      CLKOUT2_DIVIDE => CLK_USER1_DIV,-- Division factor for CLKOUT2 (1 to 128)
      CLKOUT2_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT2 (0.01 to 0.99)
      CLKOUT2_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT2 (0.0 to 360.0)
      CLKOUT3_DIVIDE => CLK_USER2_DIV,-- Division factor for CLKOUT3 (1 to 128)
      CLKOUT3_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT3 (0.01 to 0.99)
      CLKOUT3_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT3 (0.0 to 360.0)
      CLKOUT4_DIVIDE => CLK_USER3_DIV,-- Division factor for CLKOUT4 (1 to 128)
      CLKOUT4_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT4 (0.01 to 0.99)
      CLKOUT4_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT4 (0.0 to 360.0)
      CLKOUT5_DIVIDE => CLK_USER4_DIV,-- Division factor for CLKOUT5 (1 to 128)
      CLKOUT5_DUTY_CYCLE => 0.5, -- Duty cycle for CLKOUT5 (0.01 to 0.99)
      CLKOUT5_PHASE => 0.0,      -- Phase shift (degrees) for CLKOUT5 (0.0 to 360.0)
      COMPENSATION => "INTERNAL",  -- "SYSTEM_SYNCHRNOUS", 
                                             -- "SOURCE_SYNCHRNOUS", "INTERNAL", 
                                             -- "EXTERNAL", "DCM2PLL", "PLL2DCM" 
      DIVCLK_DIVIDE => 1,      -- Division factor for all clocks (1 to 52)
      REF_JITTER => 0.100)     -- Input reference jitter (0.000 to 0.999 UI%)
   port map (
      CLKFBOUT => pll1_fb,      -- General output feedback signal
      CLKOUT0 => pll1_clk0,        -- One of six general clock output signals
      CLKOUT1 => pll1_clk1,        -- One of six general clock output signals
      CLKOUT2 => pll1_clk2,        -- One of six general clock output signals
      CLKOUT3 => pll1_clk3,        -- One of six general clock output signals
      CLKOUT4 => pll1_clk4,        -- One of six general clock output signals
      CLKOUT5 => pll1_clk5,        -- One of six general clock output signals
      LOCKED => pll1_locked,          -- Active high PLL lock signal
      CLKFBIN => pll1_fb,        -- Clock feedback input
      CLKIN => pll0_clk0_buf,           -- Clock input
      RST => pll1_reset          -- Asynchronous PLL reset
   );

   pll1_reset <= RESET or not pll0_locked;

   -- Global clock buffers for clocks
   clk0_bufg_inst1 : BUFG
   port map(i => pll1_clk0,
            o => pll1_clk0_buf);
   clk1_bufg_inst1 : BUFG
   port map(i => pll1_clk1,
            o => pll1_clk1_buf);
   clk2_bufg_inst1 : BUFG
   port map(i => pll1_clk2,
            o => pll1_clk2_buf);
   clk3_bufg_inst1 : BUFG
   port map(i => pll1_clk3,
            o => pll1_clk3_buf);
   clk4_bufg_inst1 : BUFG
   port map(i => pll1_clk4,
            o => pll1_clk4_buf);
   clk5_bufg_inst1 : BUFG
   port map(i => pll1_clk5,
            o => pll1_clk5_buf);

   -- Port mapping of clock buffers outputs
   CLK_ICS_OUT       <= pll1_clk0_buf;
   CLK_USER0_OUT     <= pll1_clk1_buf;
   CLK_USER1_OUT     <= pll1_clk2_buf;
   CLK_USER2_OUT     <= pll1_clk3_buf;
   CLK_USER3_OUT     <= pll1_clk4_buf;
   CLK_USER4_OUT     <= pll1_clk5_buf;

   LOCK <= pll0_locked and pll1_locked;

end architecture full;
