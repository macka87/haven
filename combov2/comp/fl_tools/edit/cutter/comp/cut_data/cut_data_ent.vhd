-- cut_data_ent.vhd: FrameLink cutter: cut data logic
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

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cut_data is
   generic(
      DATA_WIDTH    : integer := 32; -- FrameLink width
      DATA_BYTES    : integer := 4; -- Width of data bus in bytes
      PART          : integer := 0; -- Number of processed part, 0 = first part
      MAX_PARTS     : integer := 4; -- Maximum number of frame parts
      MAX_PART_SIZE : integer := 512; -- Maximal size of one frame part (in bytes)
      OFFSET        : integer := 0; -- Position from SOP, 0 = first byte
      SIZE          : integer := 1  -- Extracted block size, greater than 0
   );
   port(
      CLK          : in std_logic;

      -- inputs
      DATA         : in std_logic_vector(DATA_WIDTH-1 downto 0); -- Input FrameLink data
      PART_NUM     : in std_logic_vector(log2(MAX_PARTS)-1 downto 0); -- Number of currently processed part
      WORD_NUM     : in std_logic_vector(log2(MAX_PART_SIZE / DATA_BYTES)-1 downto 0); -- Number of currently processed word in the part
      TRANSMIT_PROGRESS : in std_logic; -- Currently transmit in progress?

      -- outputs
      CUT_DATA  : out std_logic_vector(SIZE*8 - 1 downto 0)
   );
end entity cut_data;
