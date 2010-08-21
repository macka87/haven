-- sw_txbuf_ent.vhd: SW_TXBUF entity
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SW_TXBUF is
   generic(
      -- DATA_WIDTH in bits: only values 64 and 128 supported
      DATA_WIDTH     : integer;
      -- OUTPUT_WIDTH: Has to be lesser than DATA_WIDTH and
      -- (DATA_WIDTH/OUTPUT_WIDTH) has to be power of 2: 1, 2, 4, ...
      OUTPUT_WIDTH   : integer;
      -- number of items in Main packet memory (BlockRAM)
      BMEM_ITEMS     : integer;
      -- number of items in Control memory
      CTRL_MEM_ITEMS : integer := 16;
      -- Control data length (in bytes), which are sent as frame header
      -- this data are located in Packet memory, before the payload itself
      CONTROL_DATA_LENGTH : integer;
      -- send constant HW header for every outcomming packet
      CONSTANT_HW_HEADER_LENGTH : integer := 0;
      -- constant HW header data in Bytes (maximaly 8 Bytes)
      CONSTANT_HW_HEADER_DATA : std_logic_vector(63 downto 0) 
                     := X"0000000000000000"
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Output interface
      SOF_N          : out std_logic;
      SOP_N          : out std_logic;
      EOP_N          : out std_logic;
      EOF_N          : out std_logic;
      SRC_RDY_N      : out std_logic;
      DST_RDY_N      : in  std_logic;
      DATA_OUT       : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      REM_OUT        : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0);

      -- Internal Bus: Write Interface
      WR_ADDR        : in  std_logic_vector(31 downto 0);
      WR_DATA        : in  std_logic_vector(63 downto 0);
      WR_BE          : in  std_logic_vector(7 downto 0);
      WR_REQ         : in  std_logic;
      WR_RDY         : out std_logic;
      WR_LENGTH      : in  std_logic_vector(11 downto 0);
      WR_SOF         : in  std_logic;
      WR_EOF         : in  std_logic;

      -- Internal Bus: Read Interface
      -- Input Interface
      RD_ADDR        : in  std_logic_vector(31 downto 0);
      RD_BE          : in  std_logic_vector(7 downto 0);
      RD_REQ         : in  std_logic;
      RD_ARDY        : out std_logic;
      RD_SOF_IN      : in  std_logic;
      RD_EOF_IN      : in  std_logic;
      -- Output Interface
      RD_DATA        : out std_logic_vector(63 downto 0);
      RD_SRC_RDY     : out std_logic;
      RD_DST_RDY     : in  std_logic;

      -- Control Bus interface
      DIFF           : out std_logic_vector(log2(CTRL_MEM_ITEMS) downto 0);
      READY          : out std_logic;
      ACK            : in  std_logic;
      CTRL_OFFSET    : in  std_logic_vector(19 downto 0);
      CTRL_LENGTH    : in  std_logic_vector(11 downto 0);
      CTRL_READY     : out std_logic;
      CTRL_WRITE     : in  std_logic
   );
end entity SW_TXBUF;
