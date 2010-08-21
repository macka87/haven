--
-- buffer.vhd : Internal Bus Switch Buffer entity
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
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION -- IB Switch Buffer                 --
-- ----------------------------------------------------------------------------
      
entity IB_SWITCH_BUFFER is 
   generic(
      -- Data Width (1-128)
      DATA_WIDTH   : integer:= 64;
      -- The number of headers to be stored
      HEADER_NUM   : integer:=  1     
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- Upstream Port #0 -----------------------------------------------------
      -- input ifc --            
      IN0_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN0_SOF_N     : in  std_logic;
      IN0_EOF_N     : in  std_logic;
      IN0_WR        : in  std_logic;
      IN0_FULL      : out std_logic;      

      IN0_REQ_VEC   : in  std_logic_vector(2 downto 0);
      IN0_REQ_WE    : in  std_logic;      

      -- output ifc --      
      OUT0_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT0_DATA_VLD : out std_logic;
      OUT0_SOF_N    : out std_logic;
      OUT0_EOF_N    : out std_logic;      
      OUT0_RD_VEC   : in  std_logic_vector(2 downto 0);

      OUT0_REQ_VEC  : out std_logic_vector(2 downto 0);
      OUT0_ACK_VEC  : in  std_logic_vector(2 downto 0); 

      -- Downstream Port #1 ---------------------------------------------------
      IN1_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN1_SOF_N     : in  std_logic;
      IN1_EOF_N     : in  std_logic;
      IN1_WR        : in  std_logic;
      IN1_FULL      : out std_logic;      

      IN1_REQ_VEC   : in  std_logic_vector(2 downto 0);
      IN1_REQ_WE    : in  std_logic;      

      -- output ifc --      
      OUT1_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT1_DATA_VLD : out std_logic;
      OUT1_SOF_N    : out std_logic;
      OUT1_EOF_N    : out std_logic;      
      OUT1_RD_VEC   : in  std_logic_vector(2 downto 0);

      OUT1_REQ_VEC  : out std_logic_vector(2 downto 0);
      OUT1_ACK_VEC  : in  std_logic_vector(2 downto 0);       
      
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN2_SOF_N     : in  std_logic;
      IN2_EOF_N     : in  std_logic;
      IN2_WR        : in  std_logic;
      IN2_FULL      : out std_logic;      

      IN2_REQ_VEC   : in  std_logic_vector(2 downto 0);
      IN2_REQ_WE    : in  std_logic;      

      -- output ifc --      
      OUT2_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT2_DATA_VLD : out std_logic;
      OUT2_SOF_N    : out std_logic;
      OUT2_EOF_N    : out std_logic;      
      OUT2_RD_VEC   : in  std_logic_vector(2 downto 0);

      OUT2_REQ_VEC  : out std_logic_vector(2 downto 0);
      OUT2_ACK_VEC  : in  std_logic_vector(2 downto 0)     
   );
end IB_SWITCH_BUFFER;



