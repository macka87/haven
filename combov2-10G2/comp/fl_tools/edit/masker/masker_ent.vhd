-- masker_ent.vhd: Frame Link component to mask bits
-- Copyright (C) 2006 CESNET
-- Author(s): Radim Janalik <radim.janalik@gmail.com>
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

entity FL_MASKER is

   generic (
      FL_WIDTH       : integer := 32;     --FL width  16,32,64,128
      NUMBER_OF_WORDS      : integer :=  3;     --Number of FL_WIDTH-sized words in incoming packets of constant length 
      RX_PIPE        : boolean := true;   --Use pipeline for RX
      TX_PIPE        : boolean := true    --Use pipeline for TX
   );
   
   port (
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- FL input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(FL_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
      
      -- FL output interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(FL_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(FL_WIDTH/8)-1 downto 0);
      
      -- SW input interface
      RESET_VALUE    : in  std_logic_vector(NUMBER_OF_WORDS*FL_WIDTH-1 downto 0);--edit

      -- MI32 Interface
      MI32_DWR      : in std_logic_vector(31 downto 0);           -- Input Data           
      MI32_ADDR     : in std_logic_vector(31 downto 0);           -- Address
      MI32_RD       : in std_logic;                               -- Read Request
      MI32_WR       : in std_logic;                               -- Write Request
      MI32_BE       : in std_logic_vector(3  downto 0);           -- Byte Enable
      MI32_DRD      : out std_logic_vector(31 downto 0);          -- Output Data
      MI32_ARDY     : out std_logic;                              -- Address Ready
      MI32_DRDY     : out std_logic                               -- Data Ready
);
end entity FL_MASKER;
