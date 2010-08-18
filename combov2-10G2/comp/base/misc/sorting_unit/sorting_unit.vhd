--
-- sorting_unit.vhd: Simple sorting unit.
-- Copyright (C) 2004 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
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


-- math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sorting_unit is
   generic (
      -- Data width
      DATA_WIDTH : integer;

      -- Number of items to sort - ID width depends on this value
      SORT_ITEMS : integer;

      -- Distributed memory type - see common/dp_distmem for more info
      DISTMEM_TYPE : integer := 16
   );
   port(
      -- Common interface
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Write port
      RX_ID          : in std_logic_vector(log2(SORT_ITEMS) - 1 downto 0);
      RX_DATA        : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- Read port
      TX_ID          : out std_logic_vector(log2(SORT_ITEMS) - 1 downto 0);
      TX_DATA        : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in std_logic
   );
end entity sorting_unit;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture sorting_unit_arch of sorting_unit is
   
   constant ADDR_WIDTH : integer := log2(SORT_ITEMS) + 1;

   signal write_addr : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal read_addr  : std_logic_vector(ADDR_WIDTH - 1 downto 0);

   signal mem_di              : std_logic_vector(DATA_WIDTH downto 0);
   signal mem_doa             : std_logic_vector(DATA_WIDTH downto 0);
   signal mem_dob             : std_logic_vector(DATA_WIDTH downto 0);

   signal mem_valid_di        : std_logic_vector(0 downto 0);
   signal mem_valid_we        : std_logic;
   signal mem_valid_doa       : std_logic_vector(0 downto 0);
   signal mem_valid_dob       : std_logic_vector(0 downto 0);

   signal mux_init            : std_logic_vector(1 downto 0);
   signal mux_init_sel        : std_logic;

   signal mux_init_read_addr  : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal mux_init_write_addr : std_logic_vector(ADDR_WIDTH - 1 downto 0);

   signal reg_init_done       : std_logic;
   signal reg_init_done_we    : std_logic;

   signal tx_write_allow      : std_logic;
   signal rx_write_allow      : std_logic;

   signal cnt_init            : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal cnt_init_ce         : std_logic;

   signal cnt_write_addr      : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal cnt_write_addr_ce   : std_logic;

   -- Read address register is exactly log2(SORT_ITEMS) bits long
   -- One bit - the MSB from cnt_init is added - this bit switches between
   -- two blocks - to cover the worst case
   signal reg_read_addr       : std_logic_vector(ADDR_WIDTH - 1 downto 0);
   signal reg_read_addr_we    : std_logic;

   signal rx_valid            : std_logic;
   signal rx_valid_a          : std_logic;
   signal rx_real_valid       : std_logic;

   signal tx_valid            : std_logic;
   signal tx_valid_a          : std_logic;
   signal tx_real_valid       : std_logic;

   signal vccvec              : std_logic_vector(ADDR_WIDTH - 1 downto 0);

begin

   vccvec <= (others => '1');

   -- Some signals mapping ...


   -- RX part valid
   -- Takes valid bit from memory and additional valid bit - their XOR is
   -- exact valid bit at write address
   rx_valid    <= mem_doa(DATA_WIDTH);-- Take the MSB bit-one of the valid bits
   rx_valid_a  <= mem_valid_dob(0);

   rx_real_valid <= rx_valid xor rx_valid_a;


   -- TX part valid
   -- Does the same as RX part but the memories are swaped
   tx_valid    <= mem_dob(DATA_WIDTH);
   tx_valid_a  <= mem_valid_doa(0);

   tx_real_valid <= tx_valid xor tx_valid_a;


   rx_write_allow <= not rx_real_valid and not RX_SRC_RDY_N;
   tx_write_allow <= tx_real_valid and not TX_DST_RDY_N;
  

   -- NEG the valid bit after each write (see mux_init)
   mem_di         <= mux_init(1) & RX_DATA;
   mem_valid_di   <= mux_init(0 downto 0);


   -- Memory instantion -------------------------------------------------------
   MEMORY_U: entity work.dp_distmem
      generic map (
         distmem_type   => DISTMEM_TYPE,
         data_width     => DATA_WIDTH + 1,
         items          => SORT_ITEMS*2
      )
      port map (
         RESET       => RESET,
         -- Write port
         WCLK        => CLK,
         ADDRA       => mux_init_write_addr,
         DI          => mem_di,
         WE          => rx_write_allow,
         DOA         => mem_doa,

         -- Read port
         ADDRB       => read_addr,
         DOB         => mem_dob
      );


   -- Read valid bit memory instantion ---------------------------------------
   -- This is written by the TX interface and read by the RX interface
   RVALID_MEMORY_U: entity work.dp_distmem
      generic map (
         distmem_type   => DISTMEM_TYPE,
         data_width     => 1,
         items          => SORT_ITEMS*2
      )
      port map (
         RESET       => RESET,
         -- Write port
         WCLK        => CLK,
         ADDRA       => mux_init_read_addr,
         DI          => mem_valid_di,
         WE          => tx_write_allow,
         DOA         => mem_valid_doa,

         -- Read port
         ADDRB       => write_addr,
         DOB         => mem_valid_dob
      );


   -- register reg_read_addr ----------------------------------------------
   reg_read_addr_we <= tx_write_allow;
   reg_read_addrp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_read_addr <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_read_addr_we = '1') then
            reg_read_addr <= reg_read_addr + 1;
         end if;
      end if;
   end process;




   -- init multiplexors ---------------------------------------------------
   with reg_init_done select
      mux_init <= "00"                                            when '0',
                  (not mem_doa(DATA_WIDTH)) & (not mem_valid_doa) when '1',
                  "XX"                                            when others;
                  

   with reg_init_done select
      mux_init_write_addr <=
         cnt_init          when '0',
         write_addr        when '1',
         (others => 'X')   when others;

   with reg_init_done select
      mux_init_read_addr <=
         cnt_init          when '0',
         read_addr         when '1',
         (others => 'X')   when others;

   
   
   -- register reg_init_done ----------------------------------------------
   reg_init_done_we <= '1' when cnt_init = vccvec(ADDR_WIDTH - 1 downto 0)
                           else
                       '0';
   reg_init_donep: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_init_done <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_init_done_we = '1') then
            reg_init_done <= '1';
         end if;
      end if;
   end process;


   -- cnt_init counter
   cnt_init_ce <= not reg_init_done;
   cnt_initp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_init <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_init_ce = '1') then
            cnt_init <= cnt_init + 1;
         end if;
      end if;
   end process;


   -- cnt_write_addr counter
   cnt_write_addr_ce <= rx_write_allow;
   cnt_write_addrp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_write_addr <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_write_addr_ce = '1') then
            cnt_write_addr <= cnt_write_addr + 1;
         end if;
      end if;
   end process;


   -- Interface mapping
  write_addr <= cnt_write_addr(ADDR_WIDTH - 1) & RX_ID;
  read_addr  <= reg_read_addr;

  RX_DST_RDY_N <= rx_real_valid or (not reg_init_done);

  TX_ID <= reg_read_addr(ADDR_WIDTH - 2 downto 0);
  TX_DATA <= mem_dob(DATA_WIDTH - 1 downto 0);
  TX_SRC_RDY_N <= not tx_real_valid;



end architecture sorting_unit_arch;

