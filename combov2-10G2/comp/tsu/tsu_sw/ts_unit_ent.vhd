-- ts_unit_ent.vhd: entity of timestamp unit
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
-- TODO:
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ts_unit is
 -- PORT
 port (
   -- Global signals
   CLK   	: in std_logic;
   RESET 	: in std_logic;

   -- In / Out SW interface via MI_32
   DWR     	: in std_logic_vector(31 downto 0);
   ADDR		: in std_logic_vector(31 downto 0);
   RD		: in std_logic;
   WR		: in std_logic;
   BE		: in std_logic_vector(3 downto 0);
   DRD		: out std_logic_vector(31 downto 0);
   ARDY		: out std_logic;
   DRDY		: out std_logic;

   -- Pacodag interface
   TS  		: out std_logic_vector(63 downto 0);
   TS_DV	: out std_logic  -- timestamp is valid (one cycle)
 );
end ts_unit;
