-- desc_flags.vhd: Atomic flag array for desc_manager.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity SYNC_FLAGS is
   generic(
      -- items in flag array needed, one item size is 1
      ITEMS : integer;
      -- flags data width
      DATA_WIDTH : integer := 1
   );
   port(
      -- write clock
      CLK      : in std_logic;
      -- reset isn't used!
      RESET    : in std_logic;

      -- get value
      GET      : out std_logic;       
      -- get address
      GET_ADDR : in std_logic_vector(log2(ITEMS)-1 downto 0);
      -- set enable
      SET      : in std_logic;
      -- set address
      SET_ADDR : in std_logic_vector(log2(ITEMS)-1 downto 0);
      -- clear enable
      CLR      : in std_logic;
      -- clear address
      CLR_ADDR : in std_logic_vector(log2(ITEMS)-1 downto 0)

   );
end entity SYNC_FLAGS;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SYNC_FLAGS is
   
   -- compute best DISTMEM_TYPE value
   function DISTMEM_TYPE_VALUE 
      return integer is
   begin
      if ITEMS <= 16 then return 16;
      elsif ITEMS <= 32 then return 32;
      else return 64;
      end if;
   end function;

   -- data out signals used for data input
   signal set_doa    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal set_doa_n  : std_logic_vector(DATA_WIDTH-1 downto 0); 
   signal clr_doa    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal clr_doa_n  : std_logic_vector(DATA_WIDTH-1 downto 0);

   -- output gets signals from two dp_distmem
   signal get_1      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal get_2      : std_logic_vector(DATA_WIDTH-1 downto 0);

begin
    
   -- generate negative SET ang CLR signal 
   GEN_NOT : for i in 0 to DATA_WIDTH-1 generate
       set_doa_n(i) <= not set_doa(i);
       clr_doa_n(i) <= not clr_doa(i);
   end generate;
       
   -- first double-port distrubuted memory
   FLAG_ARRAY_SET : entity work.dp_distmem
      generic map(
         -- Data Width
         DATA_WIDTH  => DATA_WIDTH,
         -- Item in memory needed, one item size is DATA_WIDTH
         ITEMS  => ITEMS,
         -- Distributed Ram Type(capacity) only 16, 32, 64 bits
         DISTMEM_TYPE => DISTMEM_TYPE_VALUE,   
         -- debug prints
         DEBUG   => false
      )
      port map(
         -- Common interface
         RESET  => RESET,
         -- R/W Port
         DI     => set_doa_n,
         WE     => SET,
         WCLK   => CLK,
         ADDRA  => SET_ADDR,
         DOA    => set_doa,
         -- Read Port
         ADDRB  => GET_ADDR,
         DOB    => get_1
      );

   -- second double-port distrubuted memory
   FLAG_ARRAY_CLR : entity work.dp_distmem
      generic map(
         -- Data Width
         DATA_WIDTH  => DATA_WIDTH,
         -- Item in memory needed, one item size is DATA_WIDTH
         ITEMS  => ITEMS,
         -- Distributed Ram Type(capacity) only 16, 32, 64 bits
         DISTMEM_TYPE => DISTMEM_TYPE_VALUE,     
         -- debug prints
         DEBUG   => false
      )
      port map(
         -- Common interface
         RESET  => RESET,
         -- R/W Port
         DI     => clr_doa_n,
         WE     => CLR,
         WCLK   => CLK,
         ADDRA  => CLR_ADDR,
         DOA    => clr_doa,
         -- Read Port
         ADDRB  => GET_ADDR,
         DOB    => get_2
      );

      -- global get signal
      GET <= (get_1(0) xor get_2(0));

end architecture full;

