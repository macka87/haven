--
-- ibmi64_memory.vhd: IBMI64 memory
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Pavol Korcek <korcek@liberouter.org> 
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
entity IBMI64MEM_NOREC is
   generic(
      SIZE         : integer:=1024; -- Size of memory in bytes
      BRAM_DISTMEM : integer:=0     -- 0 = BRAM / 1 = DISTMEM
    );
   port (
      -- Common Interface
      CLK              : in std_logic;
      RESET            : in std_logic;
      -- IBMI64 Interface
      WRITE_ADDR      : in std_logic_vector(31 downto 0);       -- Address
      WRITE_DATA      : in std_logic_vector(63 downto 0);       -- Data
      WRITE_BE        : in std_logic_vector(7 downto 0);        -- Byte Enable
      WRITE_REQ       : in std_logic;                           -- Write Request
      WRITE_RDY       : out std_logic;                          -- Ready
      --WRITE_LENGTH    : in std_logic_vector(11 downto 0);       -- Length
      --WRITE_SOF       : in std_logic;                           -- Start of Frame
      --WRITE_EOF       : in std_logic;   

      READ_ADDR       : in std_logic_vector(31 downto 0);       -- Address
      READ_BE         : in std_logic_vector(7 downto 0);        -- Byte Enable
      READ_REQ        : in std_logic;                           -- Read Request
      READ_ARDY       : out std_logic;                          -- Address Ready
      --READ_SOF        : out std_logic;                          -- Start of Frame (Input)
      --READ_EOF        : out std_logic;                          -- End of Frame (Intput)
      READ_DATA       : out std_logic_vector(63 downto 0);      -- Read Data
      READ_SRC_RDY    : out std_logic;                          -- Data Ready
      READ_DST_RDY    : in std_logic                           -- Endpoint Ready 
   );
end entity IBMI64MEM_NOREC;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IBMI64MEM_ARCH of IBMI64MEM_NOREC is

   signal rw_doa     : std_logic_vector(63 downto 0);
   signal data_in_be : std_logic_vector(63 downto 0);
   signal read_req_sig   : std_logic;

begin

GENERATE_BRAM: if (BRAM_DISTMEM = 0) generate

WRITE_RDY <= WRITE_REQ;
read_req_sig <= READ_REQ and READ_DST_RDY;
READ_ARDY <= read_req_sig;

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
      WEA        => WRITE_REQ,
      ADDRA      => WRITE_ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DIA        => WRITE_DATA,
      BEA        => WRITE_BE,
      DOA_DV     => open,
      DOA        => open,

      -- Interface B (read)
      CLKB       => CLK,
      PIPE_ENB   => READ_DST_RDY,
      REB        => read_req_sig,
      WEB        => '0',
      ADDRB      => READ_ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DIB        => X"0000000000000000",
      BEB        => READ_BE,
      DOB_DV     => READ_SRC_RDY,
      DOB        => READ_DATA
   );
end generate;



GENERATE_DISTMEM: if (BRAM_DISTMEM = 1) generate

WRITE_RDY    <= WRITE_REQ;
READ_ARDY    <= READ_REQ and READ_DST_RDY;
READ_SRC_RDY <= READ_REQ;

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
      WE          => WRITE_REQ,
      WCLK        => CLK,
      ADDRA       => WRITE_ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DOA         => rw_doa,
      -- Read Port
      ADDRB       => READ_ADDR(LOG2(SIZE*8/64)+2 downto 3),
      DOB         => READ_DATA 
      );

BE_P : process(WRITE_BE, WRITE_DATA, rw_doa)
begin
   for i in 0 to 7 loop
      if WRITE_BE(i) = '1' then
         data_in_be(i*8+7 downto i*8) <= WRITE_DATA(i*8+7 downto i*8);
      else
         data_in_be(i*8+7 downto i*8) <= rw_doa(i*8+7 downto i*8);
      end if;
   end loop;
end process;

end generate;




end architecture IBMI64MEM_ARCH;
