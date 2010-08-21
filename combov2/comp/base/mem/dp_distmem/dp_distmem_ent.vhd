--
-- dp_distmem_ent.vhd: Generic dual-port distributed memory (entity declaration)
-- Copyright (C) 2005 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.distmem_func.all;

-- pragma translate_off
library UNISIM;
use UNISIM.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity DP_DISTMEM is
   generic(
      -- Data Width
      DATA_WIDTH  : integer := 128;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer := 64;
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE : integer := 16;
      -- debug prints
      DEBUG   : boolean := false
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDRA  : in std_logic_vector (LOG2(ITEMS)-1 downto 0);
      DOA    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Read Port
      ADDRB  : in std_logic_vector (LOG2(ITEMS)-1 downto 0);
      DOB    : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
end entity DP_DISTMEM;
