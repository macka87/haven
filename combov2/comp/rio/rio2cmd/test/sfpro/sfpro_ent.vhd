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
      LCLKF     : inout std_logic;
      FCLK      : inout std_logic;
      ECLKP     : inout std_logic;
      ECLKN     : inout std_logic;
      ETHCLKP   : inout std_logic;
      ETHCLKN   : inout std_logic;
      -- LED:
      XLED      : inout std_logic_vector(3 downto 0);
      -- SFP:
      TXDISA    : inout std_logic;
      TXFAULTA  : inout std_logic;
      RXLOSSA   : inout std_logic;
      MODDEFA   : inout std_logic_vector(2 downto 0);
      RSA       : inout std_logic;
      TXDISB    : inout std_logic;
      TXFAULTB  : inout std_logic;
      RXLOSSB   : inout std_logic;
      MODDEFB   : inout std_logic_vector(2 downto 0);
      RSB       : inout std_logic;
      TXDISC    : inout std_logic;
      TXFAULTC  : inout std_logic;
      RXLOSSC   : inout std_logic;
      MODDEFC   : inout std_logic_vector(2 downto 0);
      RSC       : inout std_logic;
      TXDISD    : inout std_logic;
      TXFAULTD  : inout std_logic;
      RXLOSSD   : inout std_logic;
      MODDEFD   : inout std_logic_vector(2 downto 0);
      RSD       : inout std_logic;
      -- RIO:
      TDN_A     : inout std_logic;
      TDP_A     : inout std_logic;
      RDP_A     : inout std_logic;
      RDN_A     : inout std_logic;
      TDN_B     : inout std_logic;
      TDP_B     : inout std_logic;
      RDP_B     : inout std_logic;
      RDN_B     : inout std_logic;
      TDN_C     : inout std_logic;
      TDP_C     : inout std_logic;
      RDP_C     : inout std_logic;
      RDN_C     : inout std_logic;
      TDN_D     : inout std_logic;
      TDP_D     : inout std_logic;
      RDP_D     : inout std_logic;
      RDN_D     : inout std_logic;
      -- RIO:
      TXN0      : inout std_logic;
      TXP0      : inout std_logic;
      RXP0      : inout std_logic;
      RXN0      : inout std_logic;
      TXN1      : inout std_logic;
      TXP1      : inout std_logic;
      RXP1      : inout std_logic;
      RXN1      : inout std_logic;
      -- IO:
      IO        : inout std_logic_vector(43 downto 24);
      IOS       : inout std_logic_vector(103 downto 0);
      -- SSRAM0:
      S0A       : inout std_logic_vector(18 downto 0);
      S0ADSP_N  : inout std_logic;
      S0ADSC_N  : inout std_logic;
      S0ADV_N   : inout std_logic;
      S0CS1_N   : inout std_logic;
      S0CS2_N   : inout std_logic;
      S0GW_N    : inout std_logic;
      S0BW_N    : inout std_logic;
      S0WE_N    : inout std_logic_vector(3 downto 0);
      S0OE_N    : inout std_logic;
      S0MODE    : inout std_logic;
      SCLK0     : inout std_logic;
      SCLK0F    : inout std_logic;
      S0D       : inout std_logic_vector(35 downto 0);
      -- SSRAM1:
      S1A       : inout std_logic_vector(18 downto 0);
      S1ADSP_N  : inout std_logic;
      S1ADSC_N  : inout std_logic;
      S1ADV_N   : inout std_logic;
      S1CS1_N   : inout std_logic;
      S1CS2_N   : inout std_logic;
      S1GW_N    : inout std_logic;
      S1BW_N    : inout std_logic;
      S1WE_N    : inout std_logic_vector(3 downto 0);
      S1OE_N    : inout std_logic;
      S1MODE    : inout std_logic;
      SCLK1     : inout std_logic;
      SCLK1F    : inout std_logic;
      S1D       : inout std_logic_vector(35 downto 0);
      -- CAM:
      CD        : inout std_logic_vector(67 downto 0);
      COP       : inout std_logic_vector(8 downto 0);
      COPV      : inout std_logic;
      CACK_N    : inout std_logic;
      CEOT      : inout std_logic;
      CMF       : inout std_logic;
      CMM_N     : inout std_logic;
      CMV       : inout std_logic;
      CFF       : inout std_logic;
      CPHASE    : inout std_logic;
      CRST_N    : inout std_logic;
      CMCLK     : inout std_logic;
      CMCLKF    : inout std_logic;
      CAD       : inout std_logic_vector(21 downto 0);
      CCE_N     : inout std_logic;
      CALE_N    : inout std_logic;
      COE_N     : inout std_logic;
      CWE_N     : inout std_logic;
      CSCLK     : inout std_logic;
      CSEN      : inout std_logic_vector(3 downto 0)
   );
end SFPRO;



