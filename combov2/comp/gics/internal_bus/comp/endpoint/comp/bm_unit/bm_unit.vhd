--
-- bm_unit.vhd : Internal Bus Endpoint Bus Master Unit entity
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--             ENTITY DECLARATION -- IB Endpoint Bus Master Unit             --
-- ----------------------------------------------------------------------------
      
entity IB_ENDPOINT_BM_UNIT is 
   generic(
      DATA_WIDTH       : integer := 64  -- data bus width
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  
 
      -- Read interface -------------------------------------------------------
      RD_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SOF_N       : in  std_logic;
      RD_EOF_N       : in  std_logic;
      RD_SRC_RDY_N   : in  std_logic;
      RD_DST_RDY_N   : out std_logic; 

      -- Completion interface -------------------------------------------------
      CPL_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      CPL_SOF_N      : in  std_logic;
      CPL_EOF_N      : in  std_logic;
      CPL_SRC_RDY_N  : in  std_logic;
      CPL_DST_RDY_N  : out std_logic;       

      -- Bus Master interface -------------------------------------------------
      BM_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      BM_SOF_N       : in  std_logic;
      BM_EOF_N       : in  std_logic;
      BM_SRC_RDY_N   : in  std_logic;
      BM_DST_RDY_N   : out std_logic;             
 
      -- DOWN multiplexed interface -------------------------------------------
      DOWN_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DOWN_SOF_N     : out std_logic;
      DOWN_EOF_N     : out std_logic;
      DOWN_SRC_RDY_N : out std_logic;
      DOWN_DST_RDY_N : in  std_logic; 

      -- UP multiplexed interface ---------------------------------------------
      UP_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      UP_SOF_N       : out std_logic;
      UP_EOF_N       : out std_logic;
      UP_SRC_RDY_N   : out std_logic;
      UP_DST_RDY_N   : in  std_logic; 

      -- G2LR DONE interface --------------------------------------------------
      RD_TAG         : in std_logic_vector(7 downto 0);
      RD_TAG_VLD     : in std_logic;   
      RD_DONE        : in std_logic;          

      -- L2GW DONE interface --------------------------------------------------
      CPL_TAG        : in std_logic_vector(7 downto 0);
      CPL_TAG_VLD    : in std_logic;   

      -- BM DONE interface ----------------------------------------------------
      BM_TAG         : out std_logic_vector(7 downto 0);
      BM_TAG_VLD     : out std_logic         
   );
end IB_ENDPOINT_BM_UNIT;



