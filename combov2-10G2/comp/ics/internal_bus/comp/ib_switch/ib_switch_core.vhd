--
-- ib_switch.vhd: Internal Bus Switch
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus package


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SWITCH_CORE is
   generic(
      -- Data Width (64/128)
      DATA_WIDTH        : integer:=64;
      -- Port 0 Address Space 
      SWITCH_BASE       : std_logic_vector(31 downto 0):=X"11111111";
      SWITCH_LIMIT      : std_logic_vector(31 downto 0):=X"44444444";
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  : std_logic_vector(31 downto 0):=X"11111111";
      DOWNSTREAM0_LIMIT : std_logic_vector(31 downto 0):=X"11111111";
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  : std_logic_vector(31 downto 0):=X"22222222"; 
      DOWNSTREAM1_LIMIT : std_logic_vector(31 downto 0):=X"22222222"
   );
   
   port(
      -- Common Interface
      IB_CLK        : in std_logic;
      IB_RESET      : in std_logic;
      -- Upstream Port
      PORT0_DOWN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT0_DOWN_SOP_N       : in  std_logic;
      PORT0_DOWN_EOP_N       : in  std_logic;
      PORT0_DOWN_SRC_RDY_N   : in  std_logic;
      PORT0_DOWN_DST_RDY_N   : out std_logic;
      PORT0_UP_DATA          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT0_UP_SOP_N         : out std_logic;
      PORT0_UP_EOP_N         : out std_logic;
      PORT0_UP_SRC_RDY_N     : out std_logic;
      PORT0_UP_DST_RDY_N     : in  std_logic;

      -- Downstream Ports
      PORT1_DOWN_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT1_DOWN_SOP_N       : out std_logic;
      PORT1_DOWN_EOP_N       : out std_logic;
      PORT1_DOWN_SRC_RDY_N   : out std_logic;
      PORT1_DOWN_DST_RDY_N   : in  std_logic;
      PORT1_UP_DATA          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT1_UP_SOP_N         : in  std_logic;
      PORT1_UP_EOP_N         : in  std_logic;
      PORT1_UP_SRC_RDY_N     : in  std_logic;
      PORT1_UP_DST_RDY_N     : out std_logic;

      PORT2_DOWN_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT2_DOWN_SOP_N       : out std_logic;
      PORT2_DOWN_EOP_N       : out std_logic;
      PORT2_DOWN_SRC_RDY_N   : out std_logic;
      PORT2_DOWN_DST_RDY_N   : in  std_logic;
      PORT2_UP_DATA          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      PORT2_UP_SOP_N         : in  std_logic;
      PORT2_UP_EOP_N         : in  std_logic;
      PORT2_UP_SRC_RDY_N     : in  std_logic;
      PORT2_UP_DST_RDY_N     : out std_logic
   );
end entity IB_SWITCH_CORE;
