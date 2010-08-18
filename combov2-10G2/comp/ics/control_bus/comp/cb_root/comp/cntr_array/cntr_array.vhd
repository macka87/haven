-- cntr_array.vhd : Array of counters with one read and two write (add and sub) 
-- interfaces
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use IEEE.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cntr_array is
   generic(
      DATA_WIDTH: integer := 8;
      SWAP_PORTS: boolean := false; -- Swap add/sub functions of ports
      FIFO_ITEMS: integer := 4;
      MASK_SET  : integer := 0;
      MASK_BITS : integer := 255
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;

      -- Zero latency reading port
      VALUE_RD : out std_logic_vector(DATA_WIDTH-1 downto 0);
      ADDR_RD  : in  std_logic_vector(3 downto 0);

      -- Substract port with one cycle latency output of original value
      ADDR_SUB : in  std_logic_vector(3 downto 0);
      VALUE_SUB: in  std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SUB  : out std_logic_vector(DATA_WIDTH-1 downto 0);
      VLD_SUB  : in  std_logic;
      
      -- Add port with input queue (lower priority than SUB port)
      ADDR_ADD : in  std_logic_vector(3 downto 0);
      VALUE_ADD: in  std_logic_vector(DATA_WIDTH-1 downto 0);
      VLD_ADD  : in  std_logic;
      FULL_ADD : out std_logic;

      -- Mask output according to MASK_SET and MASK_BITS generics
      MASK     : out std_logic_vector(15 downto 0);

      -- Is 1 if there is pending request from ADD interface.
      -- Remembers only one request -> does not work correctly
      -- if more requests to the same counter are pending.
      PEND_REQ : out std_logic_vector(15 downto 0)
   );
end entity cntr_array;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cntr_array_arch of cntr_array is

signal dmux_out   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal dmux_in    : std_logic_vector(2*DATA_WIDTH-1 downto 0);
signal amux_out   : std_logic_vector(3 downto 0);
signal amux_in    : std_logic_vector(7 downto 0);

signal mem_doa    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal mem_di     : std_logic_vector(DATA_WIDTH-1 downto 0);

signal reg_data   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_addr   : std_logic_vector(3 downto 0);
signal sel        : std_logic_vector(0 downto 0);
signal reg_sel    : std_logic;
signal en         : std_logic;
signal reg_en     : std_logic;

signal fifo_di    : std_logic_vector(DATA_WIDTH+3 downto 0);
signal fifo_do    : std_logic_vector(DATA_WIDTH+3 downto 0);
signal fifo_empty : std_logic;
signal fifo_full  : std_logic;
signal fifo_rd    : std_logic;

signal sig_mask_set:std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_mask_bits:std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_mask   : std_logic_vector(15 downto 0);

signal reg_pend   : std_logic_vector(15 downto 0);

begin

   memory: entity work.dp_distmem
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      ITEMS       => 16,
      DISTMEM_TYPE=> 16,
      DEBUG       => false
   )
   port map(
      -- Common interface
      RESET       => RESET,
      -- R/W Port
      DI          => mem_di,
      WE          => reg_en,
      WCLK        => CLK,
      ADDRA       => reg_addr,
      DOA         => mem_doa,
      -- Read Port
      ADDRB       => ADDR_RD,
      DOB         => VALUE_RD
   );

   adder_gen1 : if SWAP_PORTS = false generate
      adder_p : process(mem_doa, reg_data, reg_sel)
      begin
         mem_di <= mem_doa + reg_data + reg_sel;
      end process;
   end generate;
   adder_gen2 : if SWAP_PORTS = true generate
      adder_p : process(mem_doa, reg_data, reg_sel)
      begin
         mem_di <= mem_doa + reg_data + (not reg_sel);
      end process;
   end generate;

   ADD_FIFO: entity work.fifo_status
   generic map(
      DATA_WIDTH  => DATA_WIDTH+4,
      DISTMEM_TYPE=> 16,
      ITEMS       => FIFO_ITEMS,
      BLOCK_SIZE  => 0
   )
   port map(
      RESET       => RESET,
      CLK         => CLK,

      -- Write interface
      DATA_IN     => fifo_di,
      WRITE_REQ   => VLD_ADD,
      FULL        => fifo_full,
      LSTBLK      => open,
      STATUS      => open,

      -- Read interface
      DATA_OUT    => fifo_do,
      READ_REQ    => fifo_rd,
      EMPTY       => fifo_empty
   );
   ffo_gen1 : if SWAP_PORTS = false generate
      fifo_di <= VALUE_ADD & ADDR_ADD;
   end generate;
   fifo_gen2 : if SWAP_PORTS = true generate
      fifo_di <= (not VALUE_ADD) & ADDR_ADD;
   end generate;
   fifo_rd <= (not fifo_empty) and (not VLD_SUB);
   
   ADDR_MUX : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 4,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => amux_in,
      SEL         => sel,
      DATA_OUT    => amux_out
   );

   amux_in <= ADDR_SUB & fifo_do(3 downto 0);
   
   DATA_MUX : entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => dmux_in,
      SEL         => sel,
      DATA_OUT    => dmux_out
   );
   dmux_gen1 : if SWAP_PORTS = false generate
      dmux_in <= (not VALUE_SUB) & fifo_do(DATA_WIDTH+3 downto 4);
   end generate;
   dmux_gen2 : if SWAP_PORTS = true generate
      dmux_in <= VALUE_SUB & fifo_do(DATA_WIDTH+3 downto 4);
   end generate;

   sel(0) <= VLD_SUB;
   en <= VLD_SUB or not fifo_empty;

   -- Register data multiplexer output
   reg_data_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         reg_data <= (others => '0');
      elsif CLK'event and CLK = '1' then
         reg_data <= dmux_out;
      end if;
   end process;
   
   -- Register address multiplexer output
   reg_addr_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         reg_addr <= (others => '0');
      elsif CLK'event and CLK = '1' then
         reg_addr <= amux_out;
      end if;
   end process;

   -- Register select signal (use it as carry input to adder
   reg_sel_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         reg_sel <= '0';
      elsif CLK'event and CLK = '1' then
         reg_sel <= sel(0);
      end if;
   end process;
   
   -- Register enable
   reg_en_p : process(CLK, RESET)
   begin
      if RESET = '1' then
         reg_en <= '0';
      elsif CLK'event and CLK = '1' then
         reg_en <= en;
      end if;
   end process;

   sig_mask_set  <= conv_std_logic_vector(MASK_SET, DATA_WIDTH);
   sig_mask_bits <= conv_std_logic_vector(MASK_BITS, DATA_WIDTH);

   reg_mask_gen : for i in 0 to 15 generate
      reg_mask_p : process(CLK, RESET)
      begin
         if RESET = '1' then
            reg_mask(i) <= '0';
         elsif CLK'event and CLK = '1' then
            if reg_en = '1' and reg_addr = i then
               if (mem_di and sig_mask_bits) 
                = (sig_mask_set and sig_mask_bits) then
                  reg_mask(i) <= '0';
               else
                  reg_mask(i) <= '1';
               end if;
            end if;
         end if;
      end process;
   end generate;

   pend_g : for i in 0 to 15 generate
      reg_pend_p : process(CLK, RESET)
      begin
         if RESET = '1' then
            reg_pend(i) <= '0';
         elsif CLK'event and CLK = '1' then
            if ADDR_ADD = i and VLD_ADD = '1' then
               reg_pend(i) <= '1';
            elsif reg_addr = i and reg_en = '1' then
               reg_pend(i) <= '0';
            end if;
         end if;
      end process;
   end generate;

   PEND_REQ <= reg_pend;
   MASK <= reg_mask;
   FULL_ADD <= fifo_full;
   OUT_SUB <= mem_doa;

end architecture cntr_array_arch;
