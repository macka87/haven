-- binder_ent.vhd: FrameLink Binder top entity
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

-- Binder declarations
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BINDER is
   generic(
      -- width of one input interface. Should be multiple of 8
      INPUT_WIDTH    : integer := 16;
      -- number of input interfaces: only 2,4,8,16 supported
      INPUT_COUNT    : integer := 4;
      -- output width - most effective value is INPUT_WIDTH*INPUT_COUNT. In 
      -- other cases FL_TRANSFORMER is instantiated
      OUTPUT_WIDTH   : integer := 64;
      -- number of parts in one FrameLink frame
      FRAME_PARTS    : integer := 2;
      
      -- select BlockRAM or LUT memory
      LUT_MEMORY     : boolean := false;
      -- Number of items (INPUT_WIDTH*INPUT_COUNT wide) in LUT memory that can 
      -- be stored for each block
      LUT_BLOCK_SIZE : integer := 16;
      -- Queue choosing policy
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := round_robin;
      -- if TRUE simple version of FL_BINDER is used instead of complex one
      -- this version composes only from FL_FIFO, TRANSFORMERs and output logic
      SIMPLE_BINDER  : boolean := false;
      -- if TRUE a stupid version of FL_BINDER is used: only a multiplexer
      -- without andy FIFOs or TRANSFORMERS (needs the same input/output
      -- width, though)
      STUPID_BINDER  : boolean := false
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1 
                                                                     downto 0);
      RX_REM         : in  std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1 
                                                                     downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)
   );
end entity FL_BINDER;
