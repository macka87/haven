
-- receiver.vhd: Receiver 
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

entity fc_receiver is
   generic (
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 3;
      DATA_WIDTH        : integer;
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";
      DISCARD_BAD_PACKETS : boolean := false
   );
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- User LocalLink RX interface
      RXU_D             : out std_logic_vector(0 to DATA_WIDTH-1);
      RXU_REM           : out std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      RXU_SRC_RDY_N     : out std_logic;
      RXU_SOP_N         : out std_logic;
      RXU_EOP_N         : out std_logic;
      RXU_DST_RDY_N     : in std_logic;

      -- Aurora LocalLink RX interface
      RXA_D             : in std_logic_vector(0 to DATA_WIDTH-1);
      RXA_REM           : in std_logic_vector(0 to log2(DATA_WIDTH/8)-1);
      RXA_SRC_RDY_N     : in std_logic;
      RXA_SOP_N         : in std_logic;
      RXA_EOP_N         : in std_logic;

      -- Aurora Native Flow Control Interface
      NFC_REQ_N        : out std_logic;
      NFC_NB           : out std_logic_vector(0 to 3);
      NFC_ACK_N        : in std_logic;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : in std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : in std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                         -- asserted for a single clock).
      FRAME_ERROR    : in std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                         -- and is asserted for a single clock.
      -- Status Interface
      RX_STATUS         : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);

      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);
      D_CNT_XON   : out std_logic_vector(31 downto 0);
      D_CNT_XOFF  : out std_logic_vector(31 downto 0);
      D_FULL      : out std_logic_vector(15 downto 0)
   );
end fc_receiver;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of fc_receiver is

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

      -- Read interface
      CLK_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_DV       : out std_logic;
      EMPTY       : out std_logic
   );
end component;

component asfifo_bram_release is
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
      MARK        : in  std_logic; -- marks actual write position
      RELEASE     : in  std_logic; -- release writed data behind MARK

      -- Read interface
      CLK_RD      : in  std_logic;
      RD          : in  std_logic;
      DO          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_DV       : out std_logic;
      EMPTY       : out std_logic
   );
end component;

component buf_ctrl_fsm is
   generic (
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110"
   );
   port (
         -- Common Input
         CLK      : in std_logic;
         RESET    : in std_logic;
         
         -- Input
         STATUS   : in std_logic_vector(2 downto 0);
         NFC_ACK_N   : in std_logic;

         -- Output
         NFC_REQ_N   : out std_logic;
         NFC_NB      : out std_logic_vector(0 to 3);

         -- Debug
         D_STATE     : out std_logic_vector(1 downto 0);
         D_CNT_XON   : out std_logic_vector(31 downto 0);
         D_CNT_XOFF  : out std_logic_vector(31 downto 0)
   );
end component buf_ctrl_fsm;

   signal data_to_fifo   : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+1 downto 0);
   signal reg_data_to_fifo   : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+1 downto 0);
   signal data_from_fifo   : std_logic_vector(DATA_WIDTH+log2(DATA_WIDTH/8)+1 downto 0);
   signal data_from_fifo_dv   : std_logic;
   signal fifo_rd : std_logic;
   signal status_i : std_logic_vector(RX_STATUS_WIDTH-1 downto 0);
   signal fifo_wr : std_logic;
   signal fifo_full  : std_logic;
   signal reg_fifo_wr : std_logic;
   signal mark    : std_logic;
   signal reg_mark: std_logic;
   signal release : std_logic;
   signal cnt_full : std_logic_vector(15 downto 0);

begin

no_rxlogic_gen: if (RX_FIFO_ITEMS = 0) generate
      status_i <= (others => '0');
      data_from_fifo <= (others => '0');
      data_from_fifo_dv <= '0';
end generate;

release_gen: if ((DISCARD_BAD_PACKETS = true) and (RX_FIFO_ITEMS > 0)) generate

process (USRCLK2, RESET)
begin
   if (RESET = '1') then
      reg_data_to_fifo <= (others => '0');
      reg_fifo_wr      <= '0';
      reg_mark         <= '0';
   elsif (USRCLK2 = '1' and USRCLK2'event) then
      reg_data_to_fifo <= data_to_fifo;
      reg_fifo_wr      <= fifo_wr;
      reg_mark         <= mark;
   end if;
end process;

   asfifo_bram_release_u: asfifo_bram_release
    generic map(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n), n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        => RX_FIFO_ITEMS,

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    => 36,

      -- Data Width
      DATA_WIDTH   => DATA_WIDTH+log2(DATA_WIDTH/8)+2,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH  => RX_STATUS_WIDTH,
      AUTO_PIPELINE => TRUE
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => USRCLK2,
      WR          => fifo_wr,
      DI          => data_to_fifo,
      FULL        => fifo_full,          -- fifo overflow must be avoided by proper flow control!
      STATUS      => status_i,
      MARK        => reg_mark,
      RELEASE     => release,

      -- Read interface
      CLK_RD      => CMDCLK,
      RD          => fifo_rd,
      DO          => data_from_fifo,
      DO_DV       => data_from_fifo_dv,
      EMPTY       => open
   );

   mark     <= not (RXA_EOP_N or RXA_SRC_RDY_N);
   release  <= SOFT_ERROR or FRAME_ERROR;
end generate;

normal_gen: if ((DISCARD_BAD_PACKETS = false) and (RX_FIFO_ITEMS > 0)) generate
   asfifo_bram_u: asfifo_bram
    generic map(
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        => RX_FIFO_ITEMS,

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    => 36,

      -- Data Width
      DATA_WIDTH   => DATA_WIDTH+log2(DATA_WIDTH/8)+2,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH  => RX_STATUS_WIDTH,
      AUTO_PIPELINE => TRUE
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => USRCLK2,
      WR          => fifo_wr,
      DI          => data_to_fifo,
      FULL        => fifo_full,          -- fifo overflow must be avoided by proper flow control!
      STATUS      => status_i,

      -- Read interface
      CLK_RD      => CMDCLK,
      RD          => fifo_rd,
      DO          => data_from_fifo,
      DO_DV       => data_from_fifo_dv,
      EMPTY       => open
   );
end generate;

   data_to_fifo <= RXA_SOP_N & RXA_EOP_N & RXA_REM & RXA_D;
   fifo_wr <= not RXA_SRC_RDY_N;
   fifo_rd <= not RXU_DST_RDY_N;

   RXU_D <= data_from_fifo(DATA_WIDTH-1 downto 0);

   -- Number of valid bytes in transmitted data (valid for last data beat only - EOF asserted)
   RXU_REM <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)-1 downto DATA_WIDTH);

   RXU_EOP_N <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)) when data_from_fifo_dv = '1' else
                '1';
   RXU_SOP_N <= data_from_fifo(DATA_WIDTH+log2(DATA_WIDTH/8)+1) when data_from_fifo_dv = '1' else
                '1';

   RXU_SRC_RDY_N  <= not data_from_fifo_dv;

   RX_STATUS <= status_i;

-- Debug - full counter
process(USRCLK2)
begin
   if (USRCLK2'event and USRCLK2 = '1') then
      if (RESET = '1') then
         cnt_full <= (others => '0');
      elsif (fifo_full='1' and fifo_wr='1') then
         cnt_full <= cnt_full + 1;
      end if;
   end if;
end process;
D_FULL <= cnt_full;

-- Flow controller
buf_ctrl_fsm_u: buf_ctrl_fsm
   generic map(
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT
   )
   port map(
         -- Common Input
         CLK      => USRCLK2,
         RESET    => RESET,
         
         -- Input
         STATUS   => status_i(RX_STATUS_WIDTH-1 downto RX_STATUS_WIDTH-3),
         NFC_ACK_N   => NFC_ACK_N,

         -- Output
         NFC_REQ_N   => NFC_REQ_N,
         NFC_NB      => NFC_NB,

         -- Debug
         D_STATE     => D_STATE,
         D_CNT_XON   => D_CNT_XON,
         D_CNT_XOFF  => D_CNT_XOFF
   );

end behavioral;












