-- sw_rxbuf_ent.vhd: SW_RXBUF entity
-- Copyright (C) 2006 CESNET
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
entity SW_RXBUF is
   generic(
      -- Input data width. Only values 64 and 128 supported
      DATA_WIDTH     : integer;
      -- number of items in BlockRAM memory
      -- has to be power of 2 (2, 4, 8, ...)
      BMEM_ITEMS     : integer;
      -- maximal number of blocks in BlockRAM memory
      BMEM_MAX_BLOCKS: integer;
      -- number of items in Control memory
      CTRL_MEM_ITEMS : integer := 16;
      -- reserved space in packet memory before the payload (in Bytes)
      CONTROL_SIZE   : integer;
      -- header is present in incoming frame
      HEADER         : boolean;
      -- footer is present in incoming frame
      FOOTER         : boolean
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Internal Bus: Read Interface
      -- Input Interface
      RD_ADDR        : in  std_logic_vector(31 downto 0);
      RD_BE          : in  std_logic_vector(7 downto 0);
      RD_REQ         : in  std_logic;
      RD_ARDY        : out std_logic;
      RD_SOF_IN      : in  std_logic;
      RD_EOF_IN      : in  std_logic;
      -- Output Interface
      RD_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SRC_RDY     : out std_logic;
      RD_DST_RDY     : in  std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      
      -- remove header before storing frame into memory
      RX_SKIP_HEADER : in  std_logic;

      -- control bus interface
      CTRL_OFFSET    : out std_logic_vector(19 downto 0);
      CTRL_LENGTH    : out std_logic_vector(11 downto 0);
      CTRL_IFC       : out std_logic_vector(3 downto 0);
      INFO_READY     : out std_logic;  -- packet information is ready
      ACK            : in  std_logic;  -- info has been read
      FREE_PACKET    : in  std_logic
   );
end entity SW_RXBUF;
