-- lctrl.vhd: Liberouter control component
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas  <martinek@liberouter.org>
--            Korenek Jan     <korenek@liberouter.org>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity LCTRL is
   generic(
      BASE        : integer;
      ADDR_WIDTH  : integer;
      
      -- Identification
      PROJECT_ID     : std_logic_vector(15 downto 0):= X"0000";
      SW_MAJOR       : std_logic_vector( 7 downto 0):=   X"00";
      SW_MINOR       : std_logic_vector( 7 downto 0):=   X"00";
      HW_MAJOR       : std_logic_vector(15 downto 0):= X"0000";
      HW_MINOR       : std_logic_vector(15 downto 0):= X"0000";
      PROJECT_TEXT   : std_logic_vector(255 downto 0) :=
      X"0000000000000000000000000000000000000000000000000000000000000000"
   );
   port(
      RESET       : in std_logic;

      -- Scom inteface
      IRQ_I       : in  std_logic_vector(7 downto 0);
      SW_RESET    : out std_logic;
      IRQ         : out std_logic;
      
      -- Internal bus signals
      LBCLK       : in    std_logic;
      LBFRAME     : in    std_logic;
      LBHOLDA     : out   std_logic;
      LBAD        : inout std_logic_vector(15 downto 0);
      LBAS        : in    std_logic;
      LBRW        : in    std_logic;
      LBRDY       : out   std_logic;
      LBLAST      : in    std_logic 
   );
end entity LCTRL;
-- ----------------------------------------------------------------------------

