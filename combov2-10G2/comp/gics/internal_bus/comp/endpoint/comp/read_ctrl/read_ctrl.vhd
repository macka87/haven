--
-- read_ctrl.vhd : Internal Bus Endpoint Read Controller Entity
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

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--       ENTITY DECLARATION -- Internal Bus Endpoint Read Controller        --
-- ----------------------------------------------------------------------------
      
entity GICS_IB_ENDPOINT_READ_CTRL is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer := 64;
      -- Address Width (1-32)
      ADDR_WIDTH   : integer := 32;
      -- Data alignment (to dst. address)
      DATA_REORDER : boolean := false;
      -- The number of reads in-process
      READ_IN_PROCESS    : integer :=  1;      
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE    : t_ibrd_type := CONTINUAL
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- Input Interface ------------------------------------------------------
      IN_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N       : in  std_logic;
      IN_EOF_N       : in  std_logic;
      IN_SRC_RDY_N   : in  std_logic;
      IN_DST_RDY_N   : out std_logic;

      -- Output Interface -----------------------------------------------------
      OUT_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic;
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic;      

      -- Read Interface -------------------------------------------------------
      RD_REQ         : out std_logic;                           
      RD_ARDY_ACCEPT : in  std_logic;                           
      RD_ADDR        : out std_logic_vector(ADDR_WIDTH-1 downto 0);        
      RD_BE          : out std_logic_vector(DATA_WIDTH/8-1 downto 0);       
      RD_LENGTH      : out std_logic_vector(11 downto 0);       
      RD_SOF         : out std_logic;                           
      RD_EOF         : out std_logic;                    

      RD_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0); 
      RD_SRC_RDY     : in  std_logic;                           
      RD_DST_RDY     : out std_logic;

     -- BM Done Interface -----------------------------------------------------
      BM_TAG         : out std_logic_vector(7 downto 0);      
      BM_TAG_VLD     : out std_logic;
      
      -- Strict unit interface ------------------------------------------------
      RD_EN          : in  std_logic;
      RD_COMPLETE    : out std_logic
   );
end GICS_IB_ENDPOINT_READ_CTRL;



