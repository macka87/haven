-- reorder_ent.vhd: FrameLink cutter: Reorder logic
-- (extract and optionally remove data on defined offset in defined frame part)
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.cutter_types.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity reorder is
   generic(
      DATA_WIDTH    : integer := 32; -- FrameLink width
      DATA_BYTES    : integer := 4; -- Width of data bus in bytes
      SIZE          : integer := 1; -- Extracted block size, greater than 0
      START_WORD    : integer := 0; -- Serial number of word containing first byte of data to cut
      END_WORD      : integer := 0; -- Serial number of word containing last byte of data to cut
      START_BYTE    : integer := 0; -- Serial number of first byte of data to cut in START_WORD
      END_BYTE      : integer := 0; -- Serial number of last byte of data to cut in END_WORD
      RX_WAIT_NEED  : boolean := false -- Flag whether extra empty beat is needed to transmit all remaining reordered data
   );
   port(
      RESET             : in std_logic; -- Asynchronous reset
      CLK               : in std_logic;

      -- inputs
      DATA_IN           : in  std_logic_vector(DATA_WIDTH-1 downto 0); -- Input data
      
      RX_READY          : in std_logic; -- Cutter is ready to receive new data; otherwise RX wait cycle is required
      TRANSMIT_PROGRESS : in std_logic; -- Transmit in progress
      TRANSMIT_PAUSE    : in std_logic; -- Transmit paused (is going to continue)
      SEL_REORDER       : in std_logic; -- Determines whether to choose original or reordered data
      SEL_REORDER_END   : in std_logic; -- Determines which version of reordered data to choose
      SEL_AUX0_EN       : in t_aux_en; -- Determines which vector of enable signals to use for Auxiliary register 0
      SEL_AUX1_EN       : in t_aux_en; -- Determines which vector of enable signals to use for Auxiliary register 1
      RX_EOF            : in std_logic; -- RX_EOF; resets all counters
      REG_RX_EOP        : in std_logic; -- Registered RX_EOP
      REG2_RX_EOP       : in std_logic; -- 2x registered RX_EOP
      REG_RX_SRC_RDY    : in std_logic; -- Registered RX_SRC_RDY
      TX_DST_RDY        : in std_logic; -- TX_DST_RDY
      CNT_AUX_EN        : in std_logic; -- Enables cnt_aux
      CNT_OUTPUT_EN     : in std_logic; -- Enalbes cnt_output
      I_TX_DATA_EN      : in std_logic; -- Enables output register
 
      -- outputs
      DATA_OUT          : out  std_logic_vector(DATA_WIDTH-1 downto 0) -- Output data
   );
end entity reorder;
