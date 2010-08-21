--
-- ibmi64_memory.vhd: IBMI64 memory
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
use work.ib_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IBMI64MEM is
   generic(
      SIZE         : integer:=1024; -- Size of memory in bytes
      BRAM_DISTMEM : integer:=0     -- 0 = BRAM / 1 = DISTMEM
    );
   port (
      -- Common Interface
      CLK              : in std_logic;
      RESET            : in std_logic;
      -- IBMI64 Interface
      IBMI_WRITE64     : inout t_ibmi_write64;
      IBMI_READ64      : inout t_ibmi_read64s
   );
end entity IBMI64MEM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IBMI64MEM_ARCH of IBMI64MEM is

   signal rw_doa     : std_logic_vector(63 downto 0);
   signal data_in_be : std_logic_vector(63 downto 0);
   signal read_req   : std_logic;

begin

GENERATE_BRAM: if (BRAM_DISTMEM = 0) generate

IBMI_WRITE64.RDY <= IBMI_WRITE64.REQ;
read_req <= IBMI_READ64.REQ and IBMI_READ64.DST_RDY;
IBMI_READ64.ARDY <= read_req;

-- ----------------------------------------------------------------------------
DP_BMEM_U : entity work.DP_BMEM_BE
   generic map (
      DATA_WIDTH => 64,
      ITEMS      => SIZE*8/64
   )
   port map (
      -- Common interface
      RESET      => RESET,

      -- Interface A (write)
      CLKA       => CLK,
      PIPE_ENA   => '1',
      REA        => '0',
      WEA        => IBMI_WRITE64.REQ,
      ADDRA      => IBMI_WRITE64.ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DIA        => IBMI_WRITE64.DATA,
      BEA        => IBMI_WRITE64.BE,
      DOA_DV     => open,
      DOA        => open,

      -- Interface B (read)
      CLKB       => CLK,
      PIPE_ENB   => IBMI_READ64.DST_RDY,
      REB        => read_req,
      WEB        => '0',
      ADDRB      => IBMI_READ64.ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DIB        => X"0000000000000000",
      BEB        => IBMI_READ64.BE,
      DOB_DV     => IBMI_READ64.SRC_RDY,
      DOB        => IBMI_READ64.DATA
   );
end generate;



GENERATE_DISTMEM: if (BRAM_DISTMEM = 1) generate

IBMI_WRITE64.RDY    <= IBMI_WRITE64.REQ;
IBMI_READ64.ARDY    <= IBMI_READ64.REQ and IBMI_READ64.DST_RDY;
IBMI_READ64.SRC_RDY <= IBMI_READ64.REQ;

-- ----------------------------------------------------------------------------
DP_DISTMEM_U : entity work.DP_DISTMEM
   generic map (
      -- Data Width
      DATA_WIDTH   => 64,
      ITEMS        => SIZE*8/64,
      DISTMEM_TYPE => 32
   )
   port map (
      -- Common interface
      RESET        => RESET,
      -- R/W Port
      DI          => data_in_be,
      WE          => IBMI_WRITE64.REQ,
      WCLK        => CLK,
      ADDRA       => IBMI_WRITE64.ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DOA         => rw_doa,
      -- Read Port
      ADDRB       => IBMI_READ64.ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DOB         => IBMI_READ64.DATA 
      );

BE_P : process(IBMI_WRITE64.BE, IBMI_WRITE64.DATA, rw_doa)
begin
   for i in 0 to 7 loop
      if IBMI_WRITE64.BE(i) = '1' then
         data_in_be(i*8+7 downto i*8) <= IBMI_WRITE64.DATA(i*8+7 downto i*8);
      else
         data_in_be(i*8+7 downto i*8) <= rw_doa(i*8+7 downto i*8);
      end if;
   end loop;
end process;

end generate;




end architecture IBMI64MEM_ARCH;
