-- discard_ent.vhd: XGMII discard
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;

-- If the signal DISCARD comes to '1' and
-- there is RX_SOP = '1', this unit starts sending
-- idle to TX until RX_EOP = '1' occures.
entity xgmii_discard is
   generic (
      --+ Depth of input fifo
      FIFO_DEPTH     : integer := 0;
      --+ inserts 16bit debug counters to DEBUG(45 downto 14)
      DEBUG_COUNTERS : boolean := false
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;
      
      --+ XGMII input
      XGMII_RXC   : in std_logic_vector( 7 downto 0);
      XGMII_RXD   : in std_logic_vector(63 downto 0);
      
      --+ Ctrl of input packet borders
      RX_SOP      : in std_logic;
      RX_EOP      : in std_logic;
      
      --+ Discard request to the current packet
      --  Valid only with RX_SOP
      DISCARD     : in std_logic;
      DISCARD_VLD : in std_logic;
      FIFO_FULL   : out std_logic;

      --+ XGMII output (without frames to discard)
      XGMII_TXC   : out std_logic_vector( 7 downto 0);
      XGMII_TXD   : out std_logic_vector(63 downto 0);

      --+ Ctrl of output packet borders
      TX_SOP      : out std_logic;
      TX_EOP      : out std_logic;

      DEBUG       : out std_logic_vector(45 downto 0)
   );
end entity;

