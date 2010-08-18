--
-- prfifo_ent.vhd: Packet Release FIFO Entity
-- Copyright (C) 2007 CESNET
-- Author(s): Koritak Jan <jenda@liberouter.org>
--            Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- FIFO package
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity FL_PRFIFO is
   generic(
      MEM_TYPE       : mem_type := BRAM;
      ITEMS          : integer  := 16;
      DATA_WIDTH     : integer  := 32;
      PARTS          : integer  := 0     -- 0 - autodetect; 1,2,3 - Given value
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)

   );
end entity;
