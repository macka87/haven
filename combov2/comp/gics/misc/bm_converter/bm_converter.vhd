--
-- bm_converter.vhd: BM Converter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ---------------------------------------------------------------------------- 

entity BM_CONVERTER is
   generic(
      -- Data Width (8-128)
      DATA_WIDTH       : integer := 64
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK              : in std_logic;
      RESET            : in std_logic;
      
      -- BM interface ---------------------------------------------------------
      BM_GLOBAL_ADDR   : in  std_logic_vector(63 downto 0); 
      BM_LOCAL_ADDR    : in  std_logic_vector(31 downto 0);
      BM_LENGTH        : in  std_logic_vector(11 downto 0);
      BM_TAG           : in  std_logic_vector(7 downto 0);
      BM_TRANS_TYPE    : in  std_logic_vector(1 downto 0);
      BM_REQ           : in  std_logic;
      BM_ACK           : out std_logic;
      BM_OP_TAG        : out std_logic_vector(7 downto 0);
      BM_OP_DONE       : out std_logic;
 
      -- IB interface ---------------------------------------------------------
      IB_DATA         : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_SOF_N        : out std_logic;
      IB_EOF_N        : out std_logic;
      IB_SRC_RDY_N    : out std_logic;
      IB_DST_RDY_N    : in  std_logic;
      IB_TAG          : in  std_logic_vector(7 downto 0);
      IB_TAG_VLD      : in  std_logic
   );
end entity BM_CONVERTER;

