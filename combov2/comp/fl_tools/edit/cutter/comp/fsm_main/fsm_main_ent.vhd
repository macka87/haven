-- fsm_main_ent.vhd: FrameLink cutter: FSM Main
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
entity fsm_main is
   generic(
      DATA_WIDTH    : integer := 32; -- FrameLink width
      DATA_BYTES    : integer := 4; -- Width of data bus in bytes
      PART          : integer := 0; -- Number of processed part, 0 = first part
      MAX_PARTS     : integer := 4; -- Maximum number of frame parts
      MAX_PART_SIZE : integer := 512; -- Maximal size of one frame part (in bytes)

      START_WORD    : integer := 0; -- Serial number of word containing first byte of data to cut
      END_WORD      : integer := 0; -- Serial number of word containing last byte of data to cut
      START_BYTE    : integer := 0; -- Serial number of first byte of data to cut in START_WORD
      END_BYTE      : integer := 0; -- Serial number of last byte of data to cut in END_WORD
      RX_WAIT_NEED  : boolean := false -- Flag whether extra empty beat is needed to transmit all remaining reordered data
   );
   port(
      RESET                  : in std_logic; -- Asynchronous reset
      CLK                    : in std_logic;

      -- inputs
      TRANSMIT_PROGRESS    : in std_logic; -- Indicating transmit on RX port in progress
      PART_NUM             : in std_logic_vector(log2(MAX_PARTS)-1 downto 0); -- Number of currently processed part
      WORD_NUM             : in std_logic_vector(log2(MAX_PART_SIZE / DATA_BYTES)-1 downto 0); -- Number of currently processed word in the part
      
      I_RX_EOP             : in std_logic; -- RX_EOP with positive logic
      
      REG_RX_SOF           : in std_logic; -- Registered RX_SOF
      REG_RX_SOP           : in std_logic; -- Registered RX_SOP
      REG_RX_EOP           : in std_logic; -- Registered RX_EOP
      REG_RX_EOF           : in std_logic; -- Registered RX_EOF
      REG_RX_SRC_RDY       : in std_logic; -- Registered RX_SRC_RDY
      REG_RX_REM           : in std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0); -- Registered RX_REM
      REG2_RX_EOP          : in std_logic; -- 2x registered RX_EOP
      REG2_RX_SOP_LV       : in std_logic; -- 2x registered RX_SOP "last valid" (sampled when transmission was in progress)
 
      -- outputs
      RX_READY                : out std_logic; -- Cutter is ready to receive new data; otherwise RX wait cycle is required
      CUT_PROGRESS         : out std_logic; -- Extraction of predefined bytes in progress
      CUT_EXTRACTED        : out std_logic; -- Extraction of predefined bytes done
      SEL_REORDER          : out std_logic; -- Determines whether to choose original or reordered data
      SEL_REORDER_END      : out std_logic; -- Determines which version of reordered data to choose
      CNT_AUX_EN           : out std_logic; -- Enables cnt_aux (auxiliary counter in reorder logic module)
      SEL_AUX0_EN          : out t_aux_en; -- Determines which vector of enable signals to use for Auxiliary register 0
      SEL_AUX1_EN          : out t_aux_en; -- Determines which vector of enable signals to use for Auxiliary register 1
      CNT_OUTPUT_EN        : out std_logic; -- Enables cnt_output (output counter in reorder logic module)
      I_TX_DATA_EN         : out std_logic; -- Enables output register
      
      GENERATED_TX_SOF     : out std_logic; -- Generated TX_SOF
      GENERATED_TX_SOP     : out std_logic; -- Generated TX_SOP
      GENERATED_TX_EOP     : out std_logic; -- Generated TX_EOP
      GENERATED_TX_EOF     : out std_logic; -- Generated TX_EOF
      GENERATED_TX_SRC_RDY : out std_logic; -- Generated TX_SRC_RDY
      GENERATED_TX_REM     : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0) -- Generated TX_REM
   );
end entity fsm_main;
