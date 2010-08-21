
-- tx_buffer.vhd: Aurvc TX buffer 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all; 
use WORK.cnt_types.all;

architecture behavioral of tx_buffer is

component asfifo_bram_block is
    generic(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        : integer;

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    : integer := 0;

      -- Data Width
      DATA_WIDTH   : integer;

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH : integer;
      AUTO_PIPELINE : boolean := false
   );
   port (
      RESET       : in  std_logic;

      -- Write interface
      CLK_WR      : in  std_logic;
      WR          : in  std_logic;
      DI          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL        : out std_logic;
      STATUS      : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      BLK_END     : in  std_logic;

      -- Read interface
      CLK_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_DV       : out std_logic;
      EMPTY       : out std_logic
   );
end component;

-- Byte quota counter
signal cnt_byte_quota : std_logic_vector(31 downto 0);
signal cnt_byte_quota_ce : std_logic;

-- Buffer Control
signal buffer_wr : std_logic;
signal buffer_data_in_i : std_logic_vector((DATA_PATHS*8)+(log2(DATA_PATHS)) downto 0);
signal buffer_data_in : std_logic_vector((DATA_PATHS*9)-1 downto 0);
signal buffer_data_out : std_logic_vector((DATA_PATHS*9)-1 downto 0);
signal buffer_dv_i : std_logic;
signal buffer_status : std_logic_vector(2 downto 0);
signal buffer_blk_end : std_logic;

signal reg_buffer_read : std_logic;
signal reg_byte_quota_met : std_logic;
signal reg_byte_quota_met_set : std_logic;

begin

-- -------------------------------------------------------------
-- Buffer
asfifo_bram_block_u: asfifo_bram_block
    generic map(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        => CHANNEL_SIZE,

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    => 0,

      -- Data Width
      DATA_WIDTH   => DATA_PATHS*9,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH => 3,
      AUTO_PIPELINE  => true     
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => FLCLK,
      WR          => buffer_wr,
      DI          => buffer_data_in,
      FULL        => TX_DST_RDY_N,
      STATUS      => buffer_status,
      BLK_END     => buffer_blk_end,

      -- Read interface
      CLK_RD      => BUFFER_CLK,
      RD          => BUFFER_READ,
      DO          => buffer_data_out,
      DO_DV       => buffer_dv_i,
      EMPTY       => BUFFER_EMPTY
   );

buffer_wr <= not TX_SRC_RDY_N;
buffer_blk_end <= not TX_EOP_N;

buffer_data_in_i <= TX_REM & (not TX_EOP_N) & TX_D;
buffer_data_in_p: process(buffer_data_in_i)
begin
   buffer_data_in((DATA_PATHS*8)+(log2(DATA_PATHS)) downto 0) <= buffer_data_in_i;
   for i in (DATA_PATHS*8)+(log2(DATA_PATHS))+1 to (DATA_PATHS*9)-1 loop
      buffer_data_in(i) <= '0';
   end loop;
end process;

BUFFER_DATA <= buffer_data_out((DATA_PATHS*8)-1 downto 0);
BUFFER_DV   <= buffer_dv_i;
BUFFER_EOP  <= buffer_data_out(DATA_PATHS*8);
BUFFER_REM  <= buffer_data_out((DATA_PATHS*8)+log2(DATA_PATHS) downto (DATA_PATHS*8)+1);

-- -------------------------------------------------------------
-- Byte quota counter

process(RESET, BUFFER_CLK)
begin
   if (RESET = '1') then
      reg_buffer_read <= '0';
   elsif (BUFFER_CLK'event AND BUFFER_CLK = '1') then
      reg_buffer_read <= BUFFER_READ;
   end if;
end process;
   
cnt_byte_quota_ce <= reg_buffer_read and buffer_dv_i;
--process(RESET, BUFFER_CLK)
--begin
--   if (RESET = '1') then
--      cnt_byte_quota <= (others => '0');
--   elsif (BUFFER_CLK'event AND BUFFER_CLK = '1') then
--      if (BYTE_QUOTA_RST = '1') then
--         cnt_byte_quota <= (others => '0');
--      elsif (cnt_byte_quota_ce='1') then
--         cnt_byte_quota <= cnt_byte_quota + 1;
--      end if;
--   end if;
--end process;

cnt_write_addr_u : entity work.cnt
generic map(
   WIDTH => 32,
   DIR   => up,
   CLEAR => true
)
port map(
   RESET => RESET,
   CLK   => BUFFER_CLK,
   DO    => cnt_byte_quota,
   CLR   => BYTE_QUOTA_RST,
   CE    => cnt_byte_quota_ce
);

process(RESET, BUFFER_CLK)
begin
   if (RESET = '1') then
      reg_byte_quota_met <= '0';
   elsif (BUFFER_CLK'event AND BUFFER_CLK = '1') then
      if (BYTE_QUOTA_RST = '1') then
         reg_byte_quota_met <= '0';
      elsif (reg_byte_quota_met_set = '1') then
         reg_byte_quota_met <= '1';
      end if;
   end if;
end process;
   
reg_byte_quota_met_set <= '1' when cnt_byte_quota = conv_std_logic_vector(BYTE_QUOTA,32) else
                            '0';
BYTE_QUOTA_MET <= reg_byte_quota_met;

end behavioral;

