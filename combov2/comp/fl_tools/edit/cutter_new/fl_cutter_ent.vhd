-- fl_cutter_ent.vhd: entity of fl_cutter component
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03 at stud.fit.vutbr.cz>
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
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_cutter is
 -- GENERIKY
 generic (
   DATA_WIDTH : integer := 32;    -- FrameLink width
   PART       : integer := 0;     -- Number of processed part, 0 = first part
   -- Position of extracted data
   EXT_OFFSET : integer := 2;     -- Position from SOP (bytes), 0 = first byte
   EXT_SIZE   : integer := 4;     -- Extracted block size (bytes), greather than 0
   -- Position of cutted data - removes only whole words!
   CUT_OFFSET : integer := 4;     -- Position from SOP (words), 0 = first word
   CUT_SIZE   : integer := 0     -- Cutted block size (words) - if set to 0 then no data are removed
 );
 
 -- PORT
 port (
   CLK   : in std_logic;
   RESET : in std_logic;
   
   -- Input interface
   RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
   RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   RX_SRC_RDY_N : in  std_logic;
   RX_DST_RDY_N : out std_logic;
   RX_SOP_N     : in  std_logic;
   RX_EOP_N     : in  std_logic;
   RX_SOF_N     : in  std_logic;
   RX_EOF_N     : in  std_logic;
   
   -- Output interface
   TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
   TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   TX_SRC_RDY_N : out std_logic;
   TX_DST_RDY_N : in  std_logic;
   TX_SOP_N     : out std_logic;
   TX_EOP_N     : out std_logic;
   TX_SOF_N     : out std_logic;
   TX_EOF_N     : out std_logic;
   
   -- Extract data
   EXTRACTED_DATA  : out std_logic_vector(EXT_SIZE*8 - 1 downto 0);
   EXTRACTED_DONE  : out std_logic;  -- ext. data is done (one cycle)
   EXTRACTED_ERR   : out std_logic   -- ext. data is not correct (not enought source data etc.)
 );
end fl_cutter;
