--
-- transformer.vhd: Internal Bus Transformer
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- IB Transformer                     --
-- ---------------------------------------------------------------------------- 

entity IB_TRANSFORMER is
   generic(
      -- Upstream Data Width (2-128)
      UP_DATA_WIDTH           : integer := 64;
      -- Downstream Data Width (1-64)
      DOWN_DATA_WIDTH         : integer :=  8;      
      -- The length of upstream input buffer (>=0)
      UP_INPUT_BUFFER_ITEMS   : integer :=  0;
      -- The length of downstream input buffer (>=0)
      DOWN_INPUT_BUFFER_ITEMS : integer :=  0;      
      -- Upstream output pipe enable
      UP_OUTPUT_PIPE          : boolean := false;
      -- Downstream output pipe enable
      DOWN_OUTPUT_PIPE        : boolean := false      
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK                : in std_logic;
      RESET              : in std_logic;
      
      -- Upstream Port --------------------------------------------------------
      UP_IN_DATA         : in  std_logic_vector(UP_DATA_WIDTH-1 downto 0);
      UP_IN_SOF_N        : in  std_logic;
      UP_IN_EOF_N        : in  std_logic;
      UP_IN_SRC_RDY_N    : in  std_logic;
      UP_IN_DST_RDY_N    : out std_logic;
      
      UP_OUT_DATA        : out std_logic_vector(UP_DATA_WIDTH-1 downto 0);
      UP_OUT_SOF_N       : out std_logic;
      UP_OUT_EOF_N       : out std_logic;
      UP_OUT_SRC_RDY_N   : out std_logic;
      UP_OUT_DST_RDY_N   : in  std_logic;

      -- Downstream Port ------------------------------------------------------
      DOWN_OUT_DATA      : out std_logic_vector(DOWN_DATA_WIDTH-1 downto 0);
      DOWN_OUT_SOF_N     : out std_logic;
      DOWN_OUT_EOF_N     : out std_logic;
      DOWN_OUT_SRC_RDY_N : out std_logic;
      DOWN_OUT_DST_RDY_N : in  std_logic;
      
      DOWN_IN_DATA       : in  std_logic_vector(DOWN_DATA_WIDTH-1 downto 0);
      DOWN_IN_SOF_N      : in  std_logic;
      DOWN_IN_EOF_N      : in  std_logic;
      DOWN_IN_SRC_RDY_N  : in  std_logic;
      DOWN_IN_DST_RDY_N  : out std_logic
   );
end entity IB_TRANSFORMER;



