--
-- mi64_memory.vhd: MI32 memory
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.lb_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MI32MEM is
   generic(
      SIZE         : integer:=1024; -- Size of memory in bytes
      BRAM_DISTMEM : integer:=0     -- 0 = BRAM / 1 = DISTMEM
    );
   port (
      -- Common Interface
      CLK              : in std_logic;
      RESET            : in std_logic;
      -- MI32 Interface
      MI32             : inout t_mi32
   );
end entity MI32MEM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture MI32MEM_ARCH of MI32MEM is

   signal rw_doa     : std_logic_vector(31 downto 0);
   signal data_in_be : std_logic_vector(31 downto 0);


begin

GENERATE_BRAM: if (BRAM_DISTMEM = 0) generate
MI32.ARDY <= '1';

-- ----------------------------------------------------------------------------
DP_BMEM_U : entity work.DP_BMEM_BE
   generic map (
      DATA_WIDTH => 32,
      ITEMS      => SIZE*8/32
   )
   port map (
      -- Common interface
      RESET      => RESET,

      -- Interface A (write)
      CLKA       => CLK,
      PIPE_ENA   => '1',
      REA        => '0',
      WEA        => MI32.WR,
      ADDRA      => MI32.ADDR(LOG2(SIZE*8/32)+1 downto 2),
      DIA        => MI32.DWR,
      BEA        => MI32.BE,
      DOA_DV     => open,
      DOA        => open,

      -- Interface B (read)
      CLKB       => CLK,
      PIPE_ENB   => '1',
      REB        => MI32.RD,
      WEB        => '0',
      ADDRB      => MI32.ADDR(LOG2(SIZE*8/32)+1 downto 2),
      DIB        => X"00000000",
      BEB        => MI32.BE,
      DOB_DV     => MI32.DRDY,
      DOB        => MI32.DRD
   );
end generate;



GENERATE_DISTMEM: if (BRAM_DISTMEM = 1) generate

MI32.ARDY <= '1';
MI32.DRDY <= MI32.RD;
-- ----------------------------------------------------------------------------
DP_DISTMEM_U : entity work.DP_DISTMEM
   generic map (
      -- Data Width
      DATA_WIDTH   => 32,
      ITEMS        => SIZE*8/32,
      DISTMEM_TYPE => 32
   )
   port map (
      -- Common interface
      RESET        => RESET,
      -- R/W Port
      DI          => data_in_be,
      WE          => MI32.WR,
      WCLK        => CLK,
      ADDRA       => MI32.ADDR(LOG2(SIZE*8/32)+1 downto 2),
      DOA         => rw_doa,
      -- Read Port
      ADDRB       => MI32.ADDR(LOG2(SIZE*8/32)+1 downto 2),
      DOB         => MI32.DRD
      );

BE_P : process(MI32.BE, MI32.DWR, rw_doa)
begin
   for i in 0 to 3 loop
      if MI32.BE(i) = '1' then
         data_in_be(i*8+7 downto i*8) <= MI32.DWR(i*8+7 downto i*8);
      else
         data_in_be(i*8+7 downto i*8) <= rw_doa(i*8+7 downto i*8);
      end if;
   end loop;
end process;

end generate;




end architecture MI32MEM_ARCH;
