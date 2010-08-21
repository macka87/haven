--
-- fpga_u5.vhd: Top level FPGA design
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

entity FPGA_U5 is
   port (
      -- CLK:
      LCLKF     : in std_logic;
      LVDSFP    : in std_logic;
      LVDSFN    : in std_logic;
      CLKF      : in std_logic;
      -- IO
      X         : inout std_logic_vector(39 downto 0);
      IOS       : inout std_logic_vector(103 downto 0);
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
      RXP1      : in std_logic;
      RXN1      : in std_logic;
      TXN0      : out std_logic;
      TXP0      : out std_logic;
      RXP0      : in std_logic;
      RXN0      : in std_logic
   );
end FPGA_U5;

