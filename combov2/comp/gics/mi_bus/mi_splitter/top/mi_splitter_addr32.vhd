--
-- mi_splitter_addr32.vhd: MI Splitter wrapper with 32bit OUT_ADDRs
-- Copyright (C) 2009 CESNET
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

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ---------------------------------------------------------------------------- 

entity MI_SPLITTER_ADDR32 is
   generic(
      ITEMS       : integer;   -- number of output MI interfaces
      ADDR_WIDTH  : integer;   -- width of address spaces on output ports (1-32)
      DATA_WIDTH  : integer;   -- data width (8-128)
      PIPE        : boolean := false -- insert pipeline
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector((ADDR_WIDTH+log2(ITEMS))-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*32-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)
      
   );
end entity MI_SPLITTER_ADDR32;


architecture mi_splitter_addr32_arch of MI_SPLITTER_ADDR32 is

   signal out_addr_aux : std_logic_vector(ITEMS*ADDR_WIDTH-1 downto 0);

begin
   
   MI_SPLITTER : entity work.MI_SPLITTER
   generic map (
      ITEMS       => ITEMS,
      ADDR_WIDTH  => ADDR_WIDTH,
      DATA_WIDTH  => DATA_WIDTH,
      PIPE        => PIPE
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK         => CLK,
      RESET       => RESET,
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      => IN_DWR,
      IN_ADDR     => IN_ADDR,
      IN_BE       => IN_BE,
      IN_RD       => IN_RD,
      IN_WR       => IN_WR,
      IN_ARDY     => IN_ARDY,
      IN_DRD      => IN_DRD,
      IN_DRDY     => IN_DRDY,
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     => OUT_DWR,
      OUT_ADDR    => out_addr_aux,
      OUT_BE      => OUT_BE,
      OUT_RD      => OUT_RD,
      OUT_WR      => OUT_WR,
      OUT_ARDY    => OUT_ARDY,
      OUT_DRD     => OUT_DRD,
      OUT_DRDY    => OUT_DRDY
   );
   
   addr_gen: for i in 0 to ITEMS-1 generate
      OUT_ADDR(i*32+ADDR_WIDTH-1 downto i*32) <=
                           out_addr_aux((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH);
      OUT_ADDR((i+1)*32-1 downto i*32+ADDR_WIDTH) <= (others => '0');
   end generate;
   
end architecture;
