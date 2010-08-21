-- verification_core_ent.vhd: 
-- Copyright (C) 2010 CESNET
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity verification_core is
   generic
   (
      -- data width 
      DATA_WIDTH         : integer
   );
   port
   (
      CLK                :  in std_logic;
      RESET              :  in std_logic;

      -- input interface
      RX_DATA            :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM             :  in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N           :  in std_logic;
      RX_EOF_N           :  in std_logic;
      RX_SOP_N           :  in std_logic;
      RX_EOP_N           :  in std_logic;
      RX_SRC_RDY_N       :  in std_logic;
      RX_DST_RDY_N       : out std_logic;

      -- output interface
      TX_DATA            : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM             : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N           : out std_logic;
      TX_EOF_N           : out std_logic;
      TX_SOP_N           : out std_logic;
      TX_EOP_N           : out std_logic;
      TX_SRC_RDY_N       : out std_logic;
      TX_DST_RDY_N       :  in std_logic;

      -- MI32 interface
      MI32_DWR           :  in std_logic_vector(31 downto 0);
      MI32_ADDR          :  in std_logic_vector(31 downto 0);
      MI32_RD            :  in std_logic;
      MI32_WR            :  in std_logic;
      MI32_BE            :  in std_logic_vector(3 downto 0);
      MI32_DRD           : out std_logic_vector(31 downto 0);
      MI32_ARDY          : out std_logic;
      MI32_DRDY          : out std_logic
   );
end entity;
