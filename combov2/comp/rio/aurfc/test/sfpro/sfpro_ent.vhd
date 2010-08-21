--
-- fpga.vhd: Top level FPGA design
-- Copyright (C) 2005  CESNET
-- Author: Rudolf Cejka <cejkar@fit.vutbr.cz>
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

entity SFPRO is
   port (
      -- CLK:
      LCLKF     : in    std_logic;     -- 50MHz
      FCLK      : in    std_logic;     -- 125MHz      
      ECLKP     : in    std_logic;     -- 156.25MHz
      ECLKN     : in    std_logic;     -- NOT(ETHCLKN)
      ETHCLKP   : in    std_logic;     -- 62.5/155.52/322.26 MHz
      ETHCLKN   : in    std_logic;     -- NOT(ETHCLKP)
      -- LED:
      XLED      : out   std_logic_vector(3 downto 0);
      -- SFP:
      TXDISA    : out   std_logic;
      TXFAULTA  : in    std_logic;
      RXLOSSA   : in    std_logic;
      MODDEFA   : inout std_logic_vector(2 downto 0);
      RSA       : out   std_logic;
      
      TXDISB    : out   std_logic;
      TXFAULTB  : in    std_logic;
      RXLOSSB   : in    std_logic;
      MODDEFB   : inout std_logic_vector(2 downto 0);
      RSB       : out   std_logic;
      
      TXDISC    : out   std_logic;      
      TXFAULTC  : in    std_logic;
      RXLOSSC   : in    std_logic;
      MODDEFC   : inout std_logic_vector(2 downto 0);
      RSC       : out   std_logic;
      
      TXDISD    : out   std_logic;
      TXFAULTD  : in    std_logic;
      RXLOSSD   : in    std_logic;
      MODDEFD   : inout std_logic_vector(2 downto 0);
      RSD       : out   std_logic;
      -- RIO:
      TDN_A     : out std_logic;
      TDP_A     : out std_logic;
      RDP_A     : in  std_logic;
      RDN_A     : in  std_logic;
      TDN_B     : out std_logic;
      TDP_B     : out std_logic;
      RDP_B     : in  std_logic;
      RDN_B     : in  std_logic;
      TDN_C     : out std_logic;
      TDP_C     : out std_logic;
      RDP_C     : in  std_logic;
      RDN_C     : in  std_logic;
      TDN_D     : out std_logic;
      TDP_D     : out std_logic;
      RDP_D     : in  std_logic;
      RDN_D     : in  std_logic;
      -- RIO:
      TXN0      : out std_logic;
      TXP0      : out std_logic;
      RXP0      : in  std_logic;
      RXN0      : in  std_logic;
      TXN1      : out std_logic;
      TXP1      : out std_logic;
      RXP1      : in  std_logic;
      RXN1      : in  std_logic;
      -- IO:
      IO        : inout std_logic_vector(43 downto 24);
      IOS       : inout std_logic_vector(103 downto 0);
      -- SSRAM0:
      S0A       : out   std_logic_vector(18 downto 0);
      S0ADSP_N  : out   std_logic;
      S0ADSC_N  : out   std_logic;
      S0ADV_N   : out   std_logic;
      S0CS1_N   : out   std_logic;
      S0CS2_N   : out   std_logic;
      S0GW_N    : out   std_logic;
      S0BW_N    : out   std_logic;
      S0WE_N    : out   std_logic_vector(3 downto 0);
      S0OE_N    : out   std_logic;
      S0MODE    : out   std_logic;
      SCLK0     : out   std_logic;
      SCLK0F    : out   std_logic;
      S0D       : inout std_logic_vector(35 downto 0);
      -- SSRAM1:
      S1A       : out   std_logic_vector(18 downto 0);
      S1ADSP_N  : out   std_logic;
      S1ADSC_N  : out   std_logic;
      S1ADV_N   : out   std_logic;
      S1CS1_N   : out   std_logic;
      S1CS2_N   : out   std_logic;
      S1GW_N    : out   std_logic;
      S1BW_N    : out   std_logic;
      S1WE_N    : out   std_logic_vector(3 downto 0);
      S1OE_N    : out   std_logic;
      S1MODE    : out   std_logic;
      SCLK1     : out   std_logic;
      SCLK1F    : out   std_logic;
      S1D       : inout std_logic_vector(35 downto 0);
      -- CAM:
      CD        : inout std_logic_vector(67 downto 0);
      COP       : out   std_logic_vector(8 downto 0);
      COPV      : out   std_logic;
      CACK_N    : inout std_logic;
      CEOT      : inout std_logic;
      CMF       : in    std_logic;
      CMM_N     : in    std_logic;
      CMV       : in    std_logic;
      CFF       : in    std_logic;
      CPHASE    : out   std_logic;
      CRST_N    : out   std_logic;
      CMCLK     : out   std_logic;
      CMCLKF    : in    std_logic;
      CAD       : in    std_logic_vector(21 downto 0);
      CCE_N     : in    std_logic;
      CALE_N    : in    std_logic;
      COE_N     : in    std_logic;
      CWE_N     : in    std_logic;
      CSCLK     : inout std_logic;
      CSEN      : out   std_logic_vector(3 downto 0)
   );
end SFPRO;

