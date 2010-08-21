
-- transmitter.vhd: Transmitter 
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

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity fc_transmitter is
   generic (
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 3;
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- User LocalLink TX interface
      TXU_D             : in std_logic_vector(0 to DATA_WIDTH-1);
      TXU_REM           : in std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      TXU_SRC_RDY_N     : in std_logic;
      TXU_SOP_N         : in std_logic;
      TXU_EOP_N         : in std_logic;
      TXU_DST_RDY_N     : out std_logic;

      -- Aurora LocalLink TX interface
      TXA_D             : out std_logic_vector(0 to DATA_WIDTH-1);
      TXA_REM           : out std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      TXA_SRC_RDY_N     : out std_logic;
      TXA_SOP_N         : out std_logic;
      TXA_EOP_N         : out std_logic;
      TXA_DST_RDY_N     : in std_logic;

      -- Aurora Status Interface
      CHANNEL_UP        : in std_logic;

      -- Status Interface
      TX_STATUS         : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0)
   );
end fc_transmitter;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of fc_transmitter is

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

signal data_to_fifo   : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+1 downto 0);
signal data_from_fifo   : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+1 downto 0);
signal data_from_fifo_dv: std_logic;
signal fifo_rd          : std_logic;
signal fifo_wr          : std_logic;
signal fifo_full        : std_logic;

begin
no_txlogic_gen: if (TX_FIFO_ITEMS = 0) generate
   -- pretend the fifo is full
   fifo_full <= '1';
   TX_STATUS <= (others => '1');
   data_from_fifo <= (others => '0');
   data_from_fifo_dv <= '0';
end generate;

norm_gen: if (TX_FIFO_ITEMS > 0) generate
asfifo_bram_u: asfifo_bram
    generic map(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n), n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        => TX_FIFO_ITEMS,

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    => 36,

      -- Data Width
      DATA_WIDTH   => DATA_WIDTH+log2(DATA_WIDTH/8)+2,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH => TX_STATUS_WIDTH
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => CMDCLK,
      WR          => fifo_wr,
      DI          => data_to_fifo,
      FULL        => fifo_full,
      STATUS      => TX_STATUS,

      -- Read interface
      CLK_RD      => USRCLK2,
      RD          => fifo_rd,
      DO          => data_from_fifo,
      DO_DV       => data_from_fifo_dv,
      EMPTY       => open
   );
end generate;
data_to_fifo <= TXU_SOP_N & TXU_EOP_N & TXU_REM & TXU_D;
fifo_rd <= (not TXA_DST_RDY_N) and CHANNEL_UP;
fifo_wr <= not TXU_SRC_RDY_N;

TXU_DST_RDY_N <= fifo_full;

   TXA_D <= data_from_fifo(DATA_WIDTH-1 downto 0);

   -- Number of valid bytes in transmitted data (valid for last data beat only - EOF asserted)
   TXA_REM <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto DATA_WIDTH);

   TXA_EOP_N <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)) when data_from_fifo_dv = '1' else
                '1';
   TXA_SOP_N <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)+1)when data_from_fifo_dv = '1' else
                '1';
   TXA_SRC_RDY_N <= not (data_from_fifo_dv);

end behavioral;



