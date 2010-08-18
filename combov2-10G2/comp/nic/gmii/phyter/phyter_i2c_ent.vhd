-- phyter_i2c_ent.vhd: Phyter control & status component entity,
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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
--

library IEEE;
use IEEE.std_logic_1164.all;
-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity PHYTER_I2C is
   generic(
      BASE  : integer   -- LB base address
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- I2C interfaces
      SCL0     : inout std_logic;
      SDA0     : inout std_logic;
      SCL1     : inout std_logic;
      SDA1     : inout std_logic;
      SCL2     : inout std_logic;
      SDA2     : inout std_logic;
      SCL3     : inout std_logic;
      SDA3     : inout std_logic;

      -- Phyter disable signals
      PHDISA   : out std_logic;
      PHDISB   : out std_logic;
      PHDISC   : out std_logic;
      PHDISD   : out std_logic;

      -- Local bus signals
      LBCLK    : in    std_logic;   -- internal bus clock, up to 100 MHz
      LBFRAME  : in    std_logic;   -- Frame
      LBHOLDA  : out   std_logic;   -- Hold Ack
      LBAD     : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS     : in    std_logic;   -- Adress strobe
      LBRW     : in    std_logic;   -- Direction (Read#/Write, low : read)
      LBRDY    : out   std_logic;   -- Ready
      LBLAST   : in    std_logic    -- Last word in transfer
   );
end entity PHYTER_I2C;
