
-- rx_buffer.vhd: Aurvc RX buffer 
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

architecture behavioral of rx_buffer is

component asfifo_bram is
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
      STATUS_WIDTH : integer
   );
   port (
      RESET       : in  std_logic;

      -- Write interface
      CLK_WR      : in  std_logic;
      WR          : in  std_logic;
      DI          : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      FULL        : out std_logic;
      STATUS      : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -- Read interface
      CLK_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_DV       : out std_logic;
      EMPTY       : out std_logic
   );
end component;

component SOF_EOF_generator is
   generic (
      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true
   );   
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      CLK            : in std_logic;      -- Standart clock input
      EN             : in std_logic;      -- Enable input

      -- RX SOP/EOP signals
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;

      -- Generated EX SOF/EOF signals
      RX_SOF_N       : out std_logic;
      RX_EOF_N       : out std_logic
   );
end component;

-- Buffer Control
signal buffer_rd : std_logic;
signal buffer_data_in_i : std_logic_vector((DATA_PATHS*8)+(log2(DATA_PATHS)) downto 0);
signal buffer_data_in : std_logic_vector((DATA_PATHS*9)-1 downto 0);
signal buffer_data_out : std_logic_vector((DATA_PATHS*9)-1 downto 0);
signal buffer_dv_i : std_logic;
signal buffer_status : std_logic_vector(2 downto 0);
signal reg_sop : std_logic;
signal reg_almost_full : std_logic;
signal reg_almost_full_rst : std_logic;
signal reg_almost_full_set : std_logic;
signal sof_eof_en : std_logic;
signal rx_sop_n_i : std_logic;
signal rx_eop_n_i : std_logic;

begin

-- -------------------------------------------------------------
-- Buffer
buffer_data_in_i <= BUFFER_REM & BUFFER_EOP & BUFFER_DATA;

buffer_data_in_p: process(buffer_data_in_i)
begin
   buffer_data_in((DATA_PATHS*8)+(log2(DATA_PATHS)) downto 0) <= buffer_data_in_i;
   for i in (DATA_PATHS*8)+(log2(DATA_PATHS))+1 to (DATA_PATHS*9)-1 loop
      buffer_data_in(i) <= '0';
   end loop;
end process;

asfifo_bram_u: asfifo_bram
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
      STATUS_WIDTH => 3
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => BUFFER_CLK,
      WR          => BUFFER_WRITE,
      DI          => buffer_data_in,
      FULL        => BUFFER_FULL,
      STATUS      => buffer_status,

      -- Read interface
      CLK_RD      => FLCLK,
      RD          => buffer_rd,
      DO          => buffer_data_out,
      DO_DV       => buffer_dv_i,
      EMPTY       => open
   );

-- Generate RX_SOP signal
process(RESET, FLCLK)
begin
   if (RESET = '1') then
      reg_sop <= '1';
   elsif (FLCLK'event AND FLCLK = '1') then
      if (buffer_dv_i = '1' and RX_DST_RDY_N = '0') then
         reg_sop <= buffer_data_out(DATA_PATHS*8); -- BUFFER_EOP
      end if;
   end if;
end process;

rx_sop_n_i <= not reg_sop;
rx_eop_n_i <= not buffer_data_out(DATA_PATHS*8);

RX_D <= buffer_data_out((DATA_PATHS*8)-1 downto 0);
RX_REM <= buffer_data_out(((DATA_PATHS*8)+log2(DATA_PATHS)) downto (DATA_PATHS*8)+1);
RX_SRC_RDY_N <= not buffer_dv_i;
RX_SOP_N <= rx_sop_n_i;
RX_EOP_N <= rx_eop_n_i;
buffer_rd <= not RX_DST_RDY_N;

-- Generate RX_SOF_N and RX_EOF_N signals
sof_eof_en <= buffer_dv_i and (not RX_DST_RDY_N);
SOF_EOF_generator_u: SOF_EOF_generator
   generic map(
      RX_IS_HEADER      => RX_IS_HEADER,
      RX_IS_FOOTER      => RX_IS_FOOTER
   )   
   port map(
      -- Common Input
      RESET          => RESET,
      CLK            => FLCLK,
      EN             => sof_eof_en,

      -- RX SOP/EOP signals
      RX_SOP_N       => rx_sop_n_i,
      RX_EOP_N       => rx_eop_n_i,

      -- Generated EX SOF/EOF signals
      RX_SOF_N       => RX_SOF_N,
      RX_EOF_N       => RX_EOF_N
   );

-- -------------------------------------------------------------
-- BUFFER_ALMOST_FULL signal generator

reg_almost_full_rst <= '1' when buffer_status = XON_LIMIT else
                       '0';
reg_almost_full_set <= '1' when buffer_status = XOFF_LIMIT else
                       '0';

process(RESET, FLCLK)
begin
   if (RESET = '1') then
      reg_almost_full <= '0';
   elsif (BUFFER_CLK'event AND BUFFER_CLK = '1') then
      if (reg_almost_full_rst = '1') then
         reg_almost_full <= '0';
      elsif (reg_almost_full_set = '1') then
         reg_almost_full <= '1';
      end if;
   end if;
end process;

BUFFER_ALMOST_FULL <= reg_almost_full;
BUFFER_STATUS_IFC  <= buffer_status;

end behavioral;

