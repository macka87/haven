--
-- fpga_u16.vhd: Top level FPGA design (Spartan3E)
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

entity fpga_u16 is
port (
  -- Switch (SW0)
    SWITCH_N       : in std_logic_vector( 7 downto 0 );
  -- Ds2401 (U45)
    CSDA           : inout std_logic;
    CSCL           : out std_logic;
  -- AT88SC0104 (U18)
    SNDATA         : inout std_logic;
  -- Power Serial
    CTXD           : out std_logic;
    CRXD           : in std_logic;
    MSCL           : out std_logic;
    MSDA           : inout std_logic;
  -- Led
    CLED           : out std_logic_vector( 3 downto 0 );
  -- Pll-Set
    PLCLK          : out std_logic_vector( 10 downto 0 );
    PLLOAD_N       : out std_logic_vector( 1 downto 0 );
  -- PCI-Jtag
    PTCK           : in std_logic;
    PTDO           : out std_logic;
    PTDI           : in std_logic;
    PTMS           : in std_logic;
  -- PCI-Control
    PSMDAT         : inout std_logic;
    PWAKE_N        : out std_logic;
    PSMCLK         : inout std_logic;
    PCIEN          : in std_logic;
    PCIRST_N       : in std_logic;
  -- Oscilator (U17)
    CCLK           : in std_logic;
  -- Reset (BT1)
    RESET_N        : in std_logic;
  -- QDRII-Jtag (U10)
    CQ0TDO         : in std_logic;
    CQ0TCK         : out std_logic;
    CQ0TMS         : out std_logic;
    CQ0TDI         : out std_logic;
  -- QDRII-Jtag (U11)
    CQ1TDO         : in std_logic;
    CQ1TCK         : out std_logic;
    CQ1TMS         : out std_logic;
    CQ1TDI         : out std_logic;
  -- User-Jtag
    UTMS           : in std_logic;
    UTCK           : in std_logic;
    UTDI           : in std_logic;
    UTDO           : out std_logic;
  -- IFC1
    -- Jtag --
    IF1TMS         : out std_logic;
    IF1TDI         : out std_logic;
    IF1TDO         : in std_logic;
    IF1TCK         : out std_logic;
    IF1JTAGEN_N    : in std_logic;
    -- Config --
    IF1DONE        : in std_logic;
    IF1INIT_N      : inout std_logic;
    IF1PROG_N      : out std_logic;
    IF1CCLK        : out std_logic;
    IF1DIN         : out std_logic;
    IF1EN_N        : in std_logic;
    IF1CFG_N       : inout std_logic;
    -- I2c --
    IF1SDA         : inout std_logic;
    IF1SCLK        : out std_logic;
  -- IFC2
    -- Jtag --
    IF2TMS         : out std_logic;
    IF2TDI         : out std_logic;
    IF2TDO         : in std_logic;
    IF2TCK         : out std_logic;
    IF2JTAGEN_N    : in std_logic;
    -- Config --
    IF2DONE        : in std_logic;
    IF2INIT_N      : inout std_logic;
    IF2PROG_N      : out std_logic;
    IF2CCLK        : out std_logic;
    IF2DIN         : out std_logic;
    IF2EN_N        : in std_logic;
    IF2CFG_N       : inout std_logic;
    -- I2c --
    IF2SDA         : inout std_logic;
    IF2SCLK        : out std_logic;
  -- Virtex5 (U0)
    -- Jtag --
    FTDI           : out std_logic;
    FTCK           : out std_logic;
    FTDO           : in std_logic;
    FTMS           : out std_logic;
    -- Config --
    XRCCLK         : inout std_logic;
    XDONE          : inout std_logic;
    XPROGRAM_N     : out std_logic;
    XM0            : out std_logic;
    XRRDWR_N       : out std_logic;
    XRDIN          : out std_logic;
    XRCS_N         : out std_logic;
    XRDOUT         : in std_logic;
    XINIT_N        : inout std_logic;
    --
    XRHSH          : inout std_logic_vector( 11 downto 0 );
    XRD            : inout std_logic_vector( 7 downto 0 );
  -- PSRAM & Flash (U13 & U14)
    -- Adress --
    FA             : out std_logic_vector( 25 downto 0 );
    -- Data --
    FD             : inout std_logic_vector( 15 downto 0 );
    -- Control --
    FLB_N          : out std_logic;
    FUB_N          : out std_logic;
    FCSRAM_N       : out std_logic;
    FWE_N          : out std_logic;
    FCSFLASH_N     : out std_logic;
    FOE_N          : out std_logic;
    FBYTE_N        : out std_logic;
    FZZ_N          : out std_logic;
    FRY            : out std_logic
);
end fpga_u16;
