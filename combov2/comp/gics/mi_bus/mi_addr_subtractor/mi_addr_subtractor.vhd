-- mi_addr_subtractor.vhd: MI Address Subtractor
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ---------------------------------------------------------------------------- 

entity MI_ADDR_SUBTRACTOR is
   generic(
      -- Data width
      DATA_WIDTH  : integer := 32;
      -- Address width (1-32)
      ADDR_WIDTH  : integer;
      -- Value to subtract (base address of connected unit)
      SUBTRACT    : std_logic_vector(31 downto 0)
   );
   port(
      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      OUT_BE      : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic;
      OUT_WR      : out std_logic;
      OUT_ARDY    : in  std_logic;
      OUT_DRD     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic
   );
end entity MI_ADDR_SUBTRACTOR;

