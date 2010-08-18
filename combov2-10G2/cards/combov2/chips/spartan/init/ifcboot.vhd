-- ifcboot.vhd : ComboV2 interface card boot control (Serial SelectMAP)
-- Copyright (C) 2010 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

library UNISIM;
use UNISIM.vcomponents.all;

-- ----------------------------------------------------------------------------
--                    Architecture declaration                               --
-- ----------------------------------------------------------------------------

entity ifcboot is
   port (
      RESET     : in std_logic; -- Global async reset
      ICS_CLK   : in std_logic; -- Internal bus clock (250MHz max)
      CCLK      : in std_logic; -- Configuration interface clock (100MHz max)
      --
      BOOT_PROG : in  std_logic;-- must be high during boot
      BOOT_DATA : in  std_logic_vector(31 downto 0);
      BOOT_WEN  : in  std_logic;
      BOOT_RDY  : out std_logic;
      --
      PROG_N   : out std_logic;
      INIT_N   : in  std_logic;
      D_O      : out std_logic;
      CFG_N    : out std_logic;
      CCLK_O   : out std_logic;
      DONE     : in  std_logic
   );
end ifcboot;

architecture behavioral of ifcboot is

component ODDR2
  generic (
     DDR_ALIGNMENT : string := "NONE";
     INIT : bit := '0';
     SRTYPE : string := "SYNC"
  );
  port (
     Q : out std_ulogic;
     C0 : in std_ulogic;
     C1 : in std_ulogic;
     CE : in std_ulogic := 'H';
     D0 : in std_ulogic;
     D1 : in std_ulogic;
     R : in std_ulogic := 'L';
     S : in std_ulogic := 'L'
  );
end component;

type t_state is (IDLE, PROG, WAIT_INIT, INIT, DATA, DATA_SHIFT);
signal state, next_state : t_state;

signal regasync_prog : std_logic;
signal reg_prog    : std_logic;
signal fifo_full   : std_logic;
signal fifo_do     : std_logic_vector(31 downto 0);
signal data_reg    : std_logic_vector(31 downto 0);
signal fifo_rd     : std_logic;
signal fifo_empty  : std_logic;
signal bit_cntr    : std_logic_vector(4 downto 0);
signal cntr_rst    : std_logic;
signal cclk_en     : std_logic;
signal reg_cclk_en : std_logic;
signal cclk_n      : std_logic;
signal data_ld     : std_logic;

begin

PROG_RECLOCK: process(CCLK)
begin
   if CCLK'event and CCLK = '1' then
      if RESET = '1' then 
         regasync_prog <= '0';
         reg_prog      <= '0';
      else
         regasync_prog <= BOOT_PROG;
         reg_prog      <= regasync_prog;
      end if;
   end if;
end process;

BOOT_RDY <= not fifo_full;
FIFO: entity work.asfifo 
generic map (
   DATA_WIDTH  => 32,  -- Data Width
   ITEMS       => 16,  -- Item in memory needed, one item size is DATA_WIDTH
--   DISTMEM_TYPE => 32, -- Distributed Ram Type(capacity) only 16, 32, 64 bits
   STATUS_WIDTH => 2
)
port map (
   RESET    => RESET,
   -- Write interface
   CLK_WR   => ICS_CLK,
   DI       => BOOT_DATA,
   WR       => BOOT_WEN,
   FULL     => fifo_full,
   STATUS   => open,
   -- Read interface
   CLK_RD   => CCLK,
   DO       => fifo_do,
   RD       => fifo_rd,
   EMPTY    => fifo_empty
);

fifo_rd  <= data_ld;

DATA_SH_REG: process(CCLK, RESET)
begin
   if CCLK'event and CCLK = '1' then
      if cntr_rst = '1' then
         bit_cntr <= (others => '0');
      else
         bit_cntr <= bit_cntr + 1;
      end if;
         
      if (data_ld = '1') then 
         data_reg <= fifo_do;
      end if;
      D_O <= data_reg(conv_integer(bit_cntr));
      reg_cclk_en <= cclk_en;
   end if;
end process;

FSM_COMB: process(state, reg_prog, fifo_empty, DONE, INIT_N, bit_cntr)
begin
   PROG_N     <= '1';
   CFG_N      <= '1';
   cntr_rst   <= '1';
   cclk_en    <= '0';
   data_ld    <= '0';
   case state is
      when IDLE => 
         if (reg_prog = '1') then 
            next_state <= PROG;
         else
            next_state <= IDLE;
         end if;
      when PROG => 
         PROG_N   <= '0';
         CFG_N    <= '0';
         cntr_rst <= '0';
         if (bit_cntr = 31) then
            next_state <= WAIT_INIT;
         else
            next_state <= PROG;
         end if;
      when WAIT_INIT => 
         PROG_N   <= '0';
         CFG_N    <= '0';
         if (INIT_N = '0') then
            next_state <= INIT;
         else
            next_state <= WAIT_INIT;
         end if;
      when INIT => 
         PROG_N   <= '1';
         CFG_N    <= '0';
         if (INIT_N = '1') then
            next_state <= DATA;
         else
            next_state <= INIT;
         end if;
      when DATA =>
         CFG_N    <= '0';
         data_ld  <= '1';
         if (reg_prog = '0') then
            next_state <= IDLE;
         elsif (fifo_empty = '0') then
            next_state <= DATA_SHIFT;
         else
            next_state <= DATA;
         end if;
      when DATA_SHIFT =>
         CFG_N    <= '0';
         cclk_en  <= '1';
         cntr_rst <= '0';
         if (reg_prog = '0') then
            next_state <= IDLE;
         elsif (bit_cntr = 31) then
            next_state <= DATA;
         else
            next_state <= DATA_SHIFT;
         end if;
      when others => null;
   end case;
end process;

FSM_SEQ: process(CCLK, RESET)
begin
   if CCLK'event and CCLK = '1' then
      if RESET = '1' then
         state <= IDLE;
      else
         state <= next_state;
      end if;
   end if;
end process;

cclk_n <= not cclk;
CLOCK_OUT : ODDR2
generic map(
   DDR_ALIGNMENT => "NONE", -- Sets output alignment to "NONE", "C0", "C1"
   INIT => '0',      -- Sets initial state of the Q output to ’0’ or ’1’
   SRTYPE => "SYNC") -- Specifies "SYNC" or "ASYNC" set/reset
port map (
   Q  => CCLK_O, -- 1-bit output data
   C0 => CCLK,   -- 1-bit clock input
   C1 => cclk_n, -- 1-bit clock input
   CE => reg_cclk_en,  -- 1-bit clock enable input
   D0 => '0',    -- 1-bit data input (associated with C0)
   D1 => '1',    -- 1-bit data input (associated with C1)
   R  => '0',    -- 1-bit reset input
   S  => '0'     -- 1-bit set input
);

end behavioral;
