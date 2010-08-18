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
      CLKF      : in    std_logic;
      -- PCIe Bridge:
      LINT      : out   std_logic;
      LRESET    : in    std_logic;
      -- RIO:
      TXN3      : inout std_logic;
      TXP3      : inout std_logic;
      RXP3      : inout std_logic;
      RXN3      : inout std_logic;
      TXN2      : inout std_logic;
      TXP2      : inout std_logic;
      RXP2      : inout std_logic;
      RXN2      : inout std_logic
   );
end FPGA_U5;

