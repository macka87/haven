-- splitter_ent.vhd: FrameLink Splitter entity
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Jakub Olbert <xolber00@stud.fit.vutbr.cz>
--            Libor Polčák <polcak_l@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_TICKET_SPLITTER_FIFO2NFIFO is
   generic(
      -- Input data width - should be power of two greater than 8
      -- only 16, 32, 64, 128 supported
      RX_DATA_WIDTH  : integer := 128;
      -- Output data width - should be power of two greater than 8
      TX_DATA_WIDTH  : integer := 32;
      -- number of output interfaces
      OUTPUT_COUNT   : integer := 3;
      -- number of frame parts
      FRAME_PARTS    : integer := 2;
      -- Width of ticket in bits
      TICKET_WIDTH   : integer := 8;
      -- Number of items in input ticket FIFOs
      -- TICKET_WIDTH wide, composed of LUT memory
      TICKET_FIFO_ITEMS    : integer := 16
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(RX_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(RX_DATA_WIDTH/8)-1 downto 0);

      -- Input ticket (control) interface
      CTRL_DATA_IN      : in  std_logic_vector(TICKET_WIDTH-1 downto 0);
      CTRL_DATA_IN_VLD  : in  std_logic;
      CTRL_DATA_IN_RQ   : out std_logic;

      -- output interface
      TX_SOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector(OUTPUT_COUNT*TX_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(
                       OUTPUT_COUNT*log2(TX_DATA_WIDTH/8)-1 downto 0);

      -- Output ticket (control) interface
      CTRL_DATA_OUT     : out std_logic_vector(OUTPUT_COUNT*TICKET_WIDTH-1 downto 0);
      CTRL_DATA_OUT_VLD : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      CTRL_DATA_OUT_RQ  : in  std_logic_vector(OUTPUT_COUNT-1 downto 0)
   );
end entity FL_TICKET_SPLITTER_FIFO2NFIFO;

