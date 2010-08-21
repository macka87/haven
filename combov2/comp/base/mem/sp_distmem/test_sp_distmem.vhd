--
-- test_dp_distmem.vhd: Component for testing sp_distmem.vhd
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
--
-- README: This component is useful only for testing. We can't test
--         generic components directly. It must be encapsulated into
--         not generic component.
--         You can change testing constant in test_param.vhd
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use WORK.distmem_func.all; -- functions for enumerating generic parameters
use WORK.test_par.all;  -- constant for generic testing - TEST_*

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TEST_SP_DISTMEM is
   -- same interface like genmem_dp
   port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (LOG2(TEST_ITEMS)-1 downto 0);
      DO     : out std_logic_vector(TEST_DATA_WIDTH-1 downto 0)
      );
end entity TEST_SP_DISTMEM;




-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TEST_SP_DISTMEM_ARCH of TEST_SP_DISTMEM is

component SP_DISTMEM is
   generic(
      -- Data Width
      DATA_WIDTH  : integer;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer;
      -- Distributed Ram Type(capacity) only 16, 32, 64, 128 bits
      DISTMEM_TYPE : integer;
      -- Debug prints
      DEBUG   : boolean
   );

   port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (LOG2(ITEMS)-1 downto 0);
      DO     : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
end component;



begin
-- maping genmem_dp to TEST_GENMEM
genmem_sp_map: SP_DISTMEM
   generic map (
      DATA_WIDTH => TEST_DATA_WIDTH,
      ITEMS => TEST_ITEMS,
      DISTMEM_TYPE => TEST_DISTMEM_TYPE,
      DEBUG => TEST_DEBUG
   )
   port map(
      -- Common interface
      RESET => reset,
      -- R/W Port
      DI => di,
      WE => we,
      WCLK => wclk,
      ADDR => addr,
      DO => do
   );
end architecture TEST_SP_DISTMEM_ARCH;

