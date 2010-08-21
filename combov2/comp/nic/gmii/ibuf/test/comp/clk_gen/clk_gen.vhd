-- clk_gen.vhd: Clock generation entity 
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Jan Korenek korenek@liberouter.org 
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
--       - Do the behavioral and after PAR tests
--       - Add to top level entity

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;


-- ----------------------------------------------------------------------
--         Entity : clk_gen  
-- ----------------------------------------------------------------------
entity CLK_GEN is
   Port ( 
      -- Input 
      CLK50_IN    : in  std_logic;     -- Input clock freqvency (50MHz)
      RESET       : in  std_logic;     -- Global reset signal
      -- Output 
      CLK50_OUT   : out std_logic;  -- 50MHz  output clock
      CLK50_PH    : out std_logic;  -- 50MHz  output clock (shifted)
      CLK25       : out std_logic;  -- 25MHz  output clock
      CLK25_PH    : out std_logic;  -- 25MHz  output clock
      CLK100      : out std_logic;  -- 100MHz output clock
      CLK100_PH   : out std_logic;  -- 100MHz output clock (shifted)
      CLK200      : out std_logic;  -- 200MHz output clock
      LOCK        : out std_logic 
   );
end clk_gen;

-- ----------------------------------------------------------------------
--         Architecture : behavioral 
-- ----------------------------------------------------------------------
architecture full of CLK_GEN is

-- Component : Twice multiply freqvency 
component clk2x_mod is
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
end component;

-- component clk4x_mod is
--    port ( 
--       CLK_IN    : in std_logic;
--       RST       : in std_logic;
--       CLK4X     : out std_logic;
--       LOCK      : out std_logic
--    ); 
-- end component;   

signal clk50x100_lock : std_logic;
signal clk200_lock : std_logic;

-- ----------------------------------------------------------------------
begin

-- 100MHz generation component
CLK100_U : clk2x_mod
port map (
   CLK_IN   => CLK50_IN,
   RST      => RESET, 
   CLK1X    => CLK50_OUT, 
   CLK1X_PH => CLK50_PH, 
   CLK2X    => CLK100, 
   CLK2X_PH => CLK100_PH,
   CLK2DV   => CLK25, 
   CLK2DV_PH=> CLK25_PH, 
   LOCK     => clk50x100_lock 
);

-- 200MHz generation component
--CLK200_U : clk4x_mod
--port map ( 
--   CLK_IN => CLK50_IN,
--   RST    => RESET,
--   CLK4X  => CLK200,
--   LOCK   => clk200_lock
--); 

LOCK <= clk50x100_lock; --  and clk200_lock;

end full;
-- ----------------------------------------------------------------------
