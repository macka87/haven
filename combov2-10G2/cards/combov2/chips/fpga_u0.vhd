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
generic(
   BUILD_TIME     : std_logic_vector(31 downto 0) := X"00000000";
   BUILD_UID      : std_logic_vector(31 downto 0) := X"00000000";
   USER_GENERIC0  : std_logic_vector(31 downto 0) := X"00000000";
   USER_GENERIC1  : std_logic_vector(31 downto 0) := X"00000000";
   USER_GENERIC2  : std_logic_vector(31 downto 0) := X"00000000";
   USER_GENERIC3  : std_logic_vector(31 downto 0) := X"00000000"
);
port (
  -- PCI Express
    PCLK250_P      : in std_logic;
    PCLK250_N      : in std_logic;
    PER_P          : in std_logic_vector( 7 downto 0 );
    PER_N          : in std_logic_vector( 7 downto 0 );
    PET_P          : out std_logic_vector( 7 downto 0 );
    PET_N          : out std_logic_vector( 7 downto 0 );
    
  -- Oscilator (U3)
    PCLK0_P        : inout std_logic;
    PCLK0_N        : inout std_logic;
  -- Oscilator (U4)
    PCLK1_P        : inout std_logic;
    PCLK1_N        : inout std_logic;
  -- IFC1
    -- Clk --
    IF1_0GCLK_P    : inout std_logic;
    IF1_0GCLK_N    : inout std_logic;
    IF1_1GCLK_P    : inout std_logic;
    IF1_1GCLK_N    : inout std_logic;
    IF1_0RCLK_P    : inout std_logic;
    IF1_0RCLK_N    : inout std_logic;
    IF1_1RCLK_P    : inout std_logic;
    IF1_1RCLK_N    : inout std_logic;
    -- GTP --
    GT1R_P         : inout std_logic_vector( 3 downto 0 );
    GT1R_N         : inout std_logic_vector( 3 downto 0 );
    GT1T_P         : out std_logic_vector( 3 downto 0 );
    GT1T_N         : out std_logic_vector( 3 downto 0 );
    -- Data --
    IF1_0D_P       : inout std_logic_vector( 17 downto 0 );
    IF1_0D_N       : inout std_logic_vector( 17 downto 0 );
    IF1_1D_P       : inout std_logic_vector( 17 downto 0 );
    IF1_1D_N       : inout std_logic_vector( 17 downto 0 );
  -- IFC2
    -- Clk --
    IF2_0GCLK_P    : inout std_logic;
    IF2_0GCLK_N    : inout std_logic;
    IF2_1GCLK_P    : inout std_logic;
    IF2_1GCLK_N    : inout std_logic;
    IF2_0RCLK_P    : inout std_logic;
    IF2_0RCLK_N    : inout std_logic;
    IF2_1RCLK_P    : inout std_logic;
    IF2_1RCLK_N    : inout std_logic;
    -- GTP --
    GT2R_P         : inout std_logic_vector( 3 downto 0 );
    GT2R_N         : inout std_logic_vector( 3 downto 0 );
    GT2T_P         : out std_logic_vector( 3 downto 0 );
    GT2T_N         : out std_logic_vector( 3 downto 0 );
    -- Data --
    IF2_0D_P       : inout std_logic_vector( 17 downto 0 );
    IF2_0D_N       : inout std_logic_vector( 17 downto 0 );
    IF2_1D_P       : inout std_logic_vector( 17 downto 0 );
    IF2_1D_N       : inout std_logic_vector( 17 downto 0 );
  -- Sys Connector
    FSYS_D         : inout std_logic_vector( 19 downto 0 );
  -- PCI Clk 
    GCLK100_P      : inout std_logic;
    GCLK100_N      : inout std_logic;
    GCLK250_P      : inout std_logic;
    GCLK250_N      : inout std_logic;
  -- PLL Clk
    XCLK0_P        : inout std_logic;
    XCLK0_N        : inout std_logic;
    XCLK1_P        : inout std_logic;
    XCLK1_N        : inout std_logic;
    XCLK2_P        : inout std_logic;
    XCLK2_N        : inout std_logic;
  -- QDR-II (U10)
    -- Data --
    S0Q            : in std_logic_vector( 17 downto 0 );
    S0D            : out std_logic_vector( 17 downto 0 );
    -- Adress --
    S0A            : out std_logic_vector( 20 downto 0 );
    -- Control --
    S0BWS_N        : out std_logic_vector( 1 downto 0 );
    S0CQ_P         : in std_logic;
    S0CQ_N         : in std_logic;
    S0K_P          : out std_logic;
    S0K_N          : out std_logic;
    S0C_P          : out std_logic;
    S0C_N          : out std_logic;
    S0WPS_N        : out std_logic;
    S0RPS_N        : out std_logic;
    S0DOFF_N       : out std_logic;
  -- QDR-II (U11)
    -- Data --
    S1Q            : in std_logic_vector( 17 downto 0 );
    S1D            : out std_logic_vector( 17 downto 0 );
    -- Adress --
    S1A            : out std_logic_vector( 20 downto 0 );
    -- Control --
    S1BWS_N        : out std_logic_vector( 1 downto 0 );
    S1CQ_P         : in std_logic;
    S1CQ_N         : in std_logic;
    S1K_P          : out std_logic;
    S1K_N          : out std_logic;
    S1C_P          : out std_logic;
    S1C_N          : out std_logic;
    S1WPS_N        : out std_logic;
    S1RPS_N        : out std_logic;
    S1DOFF_N       : out std_logic;
  -- LSC1
    LSC1_D_P       : inout std_logic_vector( 17 downto 0 );
    LSC1_D_N       : inout std_logic_vector( 17 downto 0 );
  -- LSC2
    LSC2_D_P       : inout std_logic_vector( 17 downto 0 );
    LSC2_D_N       : inout std_logic_vector( 17 downto 0 );
  -- LSC3
    LSC3_D_P       : inout std_logic_vector( 10 downto 0 );
    LSC3_D_N       : inout std_logic_vector( 10 downto 0 );
  -- LSC4
    LSC4_D_P       : inout std_logic_vector( 10 downto 0 );
    LSC4_D_N       : inout std_logic_vector( 10 downto 0 );
  -- LED
    FQLED          : out std_logic_vector( 3 downto 0 );
  -- Serial
    FQTXD          : out std_logic;
    FQRXD          : in std_logic;
  -- SDRAM-DDRII (U12A)
    -- Adress --
    DA             : out std_logic_vector( 13 downto 0 );
    -- Data --
    DDQ            : inout std_logic_vector( 63 downto 0 );
    -- Control --
    DDM            : out std_logic_vector( 7 downto 0 );    
    DBA            : out std_logic_vector( 2 downto 0 );
    DCS_N          : out std_logic_vector( 1 downto 0 );
    DRAS_N         : out std_logic;
    DCAS_N         : out std_logic;
    DWE_N          : out std_logic;
    DCK0_P         : out std_logic;
    DCK0_N         : out std_logic;
    DCK1_P         : out std_logic;
    DCK1_N         : out std_logic;
    DCKE           : out std_logic_vector( 1 downto 0 );
    DDODT          : out std_logic_vector( 1 downto 0 );
    DSDA           : inout std_logic;
    DSCL           : out std_logic;
    DSA            : out std_logic_vector( 1 downto 0 );
    DDQS_P         : inout std_logic_vector( 7 downto 0 );
    DDQS_N         : inout std_logic_vector( 7 downto 0 );
  -- Oscilator (U7 & U6)
    MCLK1_P        : inout std_logic;
    MCLK1_N        : inout std_logic;
    MCLK0_P        : inout std_logic;
    MCLK0_N        : inout std_logic;
  -- Spartan3E (U16):
    XD             : inout std_logic_vector( 7 downto 0 );
    XHSH           : inout std_logic_vector( 11 downto 0 )  
);
end fpga_u0;

