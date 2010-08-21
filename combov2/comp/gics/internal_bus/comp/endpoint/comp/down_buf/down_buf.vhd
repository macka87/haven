--
-- down_buf.vhd : Internal Bus Endpoint Down Buffer Entity
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--           ENTITY DECLARATION -- Internal Bus Endpoint Down Buffer         --
-- ----------------------------------------------------------------------------
      
entity IB_ENDPOINT_DOWN_BUF is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH         : integer := 64;
      -- Endpoint Address Space 
      ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"11111111";
      ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"44444444";
      -- Endpoint is connected to
      CONNECTED_TO       : t_ib_comp := SWITCH_MASTER;
      -- Input Buffer Size
      INPUT_BUFFER_SIZE  : integer := 0
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- IB Interface ---------------------------------------------------------
      IB_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_SOF_N     : in  std_logic;
      IB_EOF_N     : in  std_logic;
      IB_SRC_RDY_N : in  std_logic;
      IB_DST_RDY_N : out std_logic;

      -- WR Interface ---------------------------------------------------------
      WR_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_SOF_N     : out std_logic;
      WR_EOF_N     : out std_logic;
      WR_SRC_RDY_N : out std_logic;
      WR_DST_RDY_N : in  std_logic;

      -- RD Interface ---------------------------------------------------------
      RD_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SOF_N     : out std_logic;
      RD_EOF_N     : out std_logic;
      RD_SRC_RDY_N : out std_logic;
      RD_DST_RDY_N : in  std_logic;      
 
     -- BM Done Interface -----------------------------------------------------
      BM_TAG       : out std_logic_vector(7 downto 0);      
      BM_TAG_VLD   : out std_logic;
      BM_DONE      : out std_logic       
   );
end IB_ENDPOINT_DOWN_BUF;



