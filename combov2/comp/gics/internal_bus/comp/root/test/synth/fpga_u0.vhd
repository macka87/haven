--
-- fpga_u0.vhd: Top level FPGA design (Virtex5)
-- Copyright (C) 2005  CESNET
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
--

library ieee;
use ieee.std_logic_1164.all;

entity fpga_u0 is
port (
  -- PCI Express
    PCLK250_P      : in std_logic;
    PCLK250_N      : in std_logic;
    --
    PER_P          : in std_logic_vector( 7 downto 0 );
    PER_N          : in std_logic_vector( 7 downto 0 );
    PET_P          : out std_logic_vector( 7 downto 0 );
    PET_N          : out std_logic_vector( 7 downto 0 );
    -- IFC1
    -- Clk --
--     IF1_0GCLK_P    : inout std_logic;
--     IF1_0GCLK_N    : inout std_logic;
--     IF1_1GCLK_P    : inout std_logic;
--     IF1_1GCLK_N    : inout std_logic;
--     IF1_0RCLK_P    : inout std_logic;
--     IF1_0RCLK_N    : inout std_logic;
--     IF1_1RCLK_P    : inout std_logic;
--     IF1_1RCLK_N    : inout std_logic;
    -- Data --
--     IF1_0D_P       : inout std_logic_vector( 17 downto 0 );
--     IF1_0D_N       : inout std_logic_vector( 17 downto 0 );
--     IF1_1D_P       : inout std_logic_vector( 17 downto 0 );
--     IF1_1D_N       : inout std_logic_vector( 17 downto 0 );
  -- IFC2
    -- Clk --
--     IF2_0GCLK_P    : inout std_logic;
--     IF2_0GCLK_N    : inout std_logic;
--     IF2_1GCLK_P    : inout std_logic;
--     IF2_1GCLK_N    : inout std_logic;
--     IF2_0RCLK_P    : inout std_logic;
--     IF2_0RCLK_N    : inout std_logic;
--     IF2_1RCLK_P    : inout std_logic;
--     IF2_1RCLK_N    : inout std_logic;
    -- Data --
--     IF2_0D_P       : inout std_logic_vector( 17 downto 0 );
--     IF2_0D_N       : inout std_logic_vector( 17 downto 0 );
--     IF2_1D_P       : inout std_logic_vector( 17 downto 0 );
--     IF2_1D_N       : inout std_logic_vector( 17 downto 0 );
  -- Sys Connector
--     FSYS_D         : inout std_logic_vector( 19 downto 0 );
  --
--     FQLED          : out std_logic_vector( 3 downto 0 );    
  -- Spartan3E (U16):
    XD             : inout std_logic_vector( 7 downto 0 );
    XHSH           : inout std_logic_vector( 11 downto 0 )  
);
end fpga_u0;
