--
-- fpga_u5.vhd: Top level FPGA design
-- Copyright (C) 2005  CESNET
-- Author: Rudolf Cejka  <cejkar  at fit.vutbr.cz>
--         Tomas Pecenka <pecenka at fit.vutbr.cz>
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
-- TODO: FIXME: Signal direction added by Tomas Pecenka
--       X signal removed, LB signals are used instead it

library ieee;
use ieee.std_logic_1164.all;

entity FPGA_U5 is
   port (
      -- CLK:
      LCLKF     : in std_logic;
      LVDSFP    : inout std_logic;
      LVDSFN    : inout std_logic;
      CLKF      : inout std_logic;
      -- LED:
      XLED      : out std_logic_vector(3 downto 0);
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
      CSEN      : out   std_logic_vector(3 downto 0);
      -- CAM COMBO6X
      CAD       : in    std_logic_vector(21 downto 0);
      CCE_N     : in    std_logic;
      CALE_N    : in    std_logic;
      COE_N     : in    std_logic;
      CWE_N     : in    std_logic;
      CSCLK     : in    std_logic;
      CSEN_N    : inout std_logic_vector(3 downto 0);
      -- SDRAM:
      DD        : inout std_logic_vector(63 downto 0);
      DCB       : inout std_logic_vector(7 downto 0);
      DBA       : inout std_logic_vector(2 downto 0);
      DQS       : inout std_logic_vector(17 downto 0);
      DA        : inout std_logic_vector(13 downto 0);
      DCS_N     : inout std_logic_vector(3 downto 0);
      DCLKE     : inout std_logic_vector(1 downto 0);
      DCAS_N    : inout std_logic;
      DRAS_N    : inout std_logic;
      DWE_N     : inout std_logic;
      DCLK      : inout std_logic;
      DCLK_N    : inout std_logic;
      DCLK2     : inout std_logic;
      RESDDR_N  : inout std_logic;
      DSDA      : inout std_logic;
      DSCLK     : inout std_logic;

      -- IO
      X         : inout std_logic_vector(39 downto 0);
      IOS       : inout std_logic_vector(103 downto 0);

      -- SSRAM0:
      S0A       : out   std_logic_vector(19 downto 0);
      S0ADSP_N  : out   std_logic;
      S0ADSC_N  : out   std_logic;
      S0ADV_N   : out   std_logic;
      S0CS1_N   : out   std_logic;
      S0CS2_N   : out   std_logic;
      S0GW_N    : out   std_logic;
      S0BW_N    : out   std_logic;
      S0WE_N    : out   std_logic_vector(3 downto 0);
      S0OE_N    : out   std_logic;
      SCLK0     : out   std_logic;
      S0D       : inout std_logic_vector(35 downto 0);
      -- SSRAM1:
      S1A       : out   std_logic_vector(19 downto 0);
      S1ADSP_N  : out   std_logic;
      S1ADSC_N  : out   std_logic;
      S1ADV_N   : out   std_logic;
      S1CS1_N   : out   std_logic;
      S1CS2_N   : out   std_logic;
      S1GW_N    : out   std_logic;
      S1BW_N    : out   std_logic;
      S1WE_N    : out   std_logic_vector(3 downto 0);
      S1OE_N    : out   std_logic;
      SCLK1     : out   std_logic;
      S1D       : inout std_logic_vector(31 downto 0);
      -- SSRAM2:
      S2A       : out   std_logic_vector(19 downto 0);
      S2ADSP_N  : out   std_logic;
      S2ADSC_N  : out   std_logic;
      S2ADV_N   : out   std_logic;
      S2CS1_N   : out   std_logic;
      S2CS2_N   : out   std_logic;
      S2GW_N    : out   std_logic;
      S2BW_N    : out   std_logic;
      S2WE_N    : out   std_logic_vector(3 downto 0);
      S2OE_N    : out   std_logic;
      SCLK2     : out   std_logic;
      S2D       : inout std_logic_vector(31 downto 0);

      -- RIO:
      TXN3      : out std_logic;
      TXP3      : out std_logic;
      RXP3      : in std_logic;
      RXN3      : in std_logic;
      TXN2      : out std_logic;
      TXP2      : out std_logic;
      RXP2      : in std_logic;
      RXN2      : in std_logic;
      TXN1      : out std_logic;
      TXP1      : out std_logic;
      RXP1      : in  std_logic;
      RXN1      : in  std_logic;
      TXN0      : out std_logic;
      TXP0      : out std_logic;
      RXP0      : in  std_logic;
      RXN0      : in  std_logic 

   );
end FPGA_U5;

