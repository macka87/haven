--
-- sp_genmem.vhd: Single Port Generic Memory
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
--
-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on

use work.math_pack.log2;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sp_genmem is
   generic(
      ADDR_WIDTH : integer := 3;
      DATA_WIDTH : integer := 1
   );
   port(
      -- Common interface
      RESET    : in  std_logic;
      CLK      : in  std_logic;

      -- Input/Output interface
      WR       : in  std_logic;
      ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity sp_genmem;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sp_genmem is

   -- sigle port memory declaration
   component RAM16X1S
   port (
      D    : in std_logic;
      WE   : in std_logic;
      WCLK : in std_logic;
      A0   : in std_logic;
      A1   : in std_logic;
      A2   : in std_logic;
      A3   : in std_logic;
      O    : out std_logic
   );
   end component;

   -- constant definition
   constant MEM_ROWS          : integer := ((2**ADDR_WIDTH+15))/16;
   constant EXADDR            : integer := log2(MEM_ROWS); -- Extra address bits
   constant FADDR             : integer := EXADDR + 4; -- Full address port

   type   t_doarr is array (0 to (MEM_ROWS-1)) of
                                std_logic_vector((DATA_WIDTH)-1 downto 0);

   -- Port A internal signals
   signal wen_i               : std_logic_vector(MEM_ROWS-1 downto 0);
   signal addr_i              : std_logic_vector(FADDR-1 downto 0);
   signal do_i                : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal do_arr              : t_doarr;

begin

-- --------------------- Memory instantion ---------------------------
addr_i(ADDR_WIDTH-1 downto 0)   <= ADDR;

-- addr inicializaton
ONE_ROWS0 : if (FADDR > ADDR_WIDTH) generate
   addr_i(FADDR-1 downto ADDR_WIDTH) <= (others => '0');
end generate;

GENMEM_COL : for i in 0 to (DATA_WIDTH-1) generate
   GENMEM_ROW : for j in 0 to (MEM_ROWS-1) generate
      RAM16X1S_U : RAM16X1S
      port map(
         D    => DI(i),
         WE   => wen_i(j),
         WCLK => CLK,
         A0   => addr_i(0),
         A1   => addr_i(1),
         A2   => addr_i(2),
         A3   => addr_i(3),
         O    => do_arr(j)(i)
      );
   end generate;
end generate;

-- --------------------- WE demultiplexor ---------------------------

MORE_ROWS1 : if (MEM_ROWS > 1) generate
-- we demultiplexor
process(addr_i, WR)
begin
   wen_i <= (others => '0');
   for i in 0 to (MEM_ROWS-1) loop
      if (conv_std_logic_vector(i, EXADDR)
          = addr_i(FADDR-1 downto FADDR-EXADDR))
      then
         wen_i(i) <= WR;
      end if;
   end loop;
end process;
end generate;

ONE_ROWS1 : if (MEM_ROWS = 1) generate
   wen_i(0) <= WR;
end generate;

-- ------------------ Output multiplexors -----------------------

MORE_ROWS2 : if (EXADDR > 0) generate
-- do output multiplexor
process(addr_i, do_arr)
begin
   do_i <= (others => '0');
   for i in 0 to (MEM_ROWS-1) loop
      if (conv_std_logic_vector(i, EXADDR)
          = addr_i(FADDR-1 downto FADDR-EXADDR))
      then
         do_i <= do_arr(i);
      end if;
   end loop;
end process;

end generate;

ONE_ROWS2 : if (EXADDR = 0) generate
   do_i <= do_arr(0);
end generate;

-- -------------------- Interface Mapping ------------------------
DO      <= do_i;

end architecture behavioral;

