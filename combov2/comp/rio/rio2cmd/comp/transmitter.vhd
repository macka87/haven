
-- transmitter.vhd: Transmitter for command protocol via RocketIO 
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
use work.rio_codes.ALL;
use work.commands.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity transmitter is
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DI       : in std_logic_vector(31 downto 0);
      DI_CMD   : in std_logic_vector(3 downto 0);
      DI_DV    : in std_logic;
      FULL     : out std_logic;

      -- RocketIO controller interface
      TXDATA   : out std_logic_vector(31 downto 0);
      TXCHARISK: out std_logic_vector(3 downto 0)
   );
end transmitter;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of transmitter is

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

component cmd_encoder is
   port (
      -- Input: command protocol
      DI       : in std_logic_vector(7 downto 0);
      DI_CMD   : in std_logic;

      -- Output: RocketIO characters
      DO       : out std_logic_vector(7 downto 0);
      DOISK    : out std_logic
   );
end component;


signal data_to_fifo     : std_logic_vector(35 downto 0);
signal data_from_fifo   : std_logic_vector(35 downto 0);
signal data_from_fifo_dv: std_logic;
signal fifo_empty       : std_logic;

signal data_to_rio      : std_logic_vector(31 downto 0);
signal k_to_rio         : std_logic_vector(3 downto 0);

signal txdata_i         : std_logic_vector(31 downto 0);
signal txcharisk_i      : std_logic_vector(3 downto 0);

-- eop logic signals
signal reg_eop          : std_logic;
signal reg_eop_set      : std_logic;
signal reg_eop_rst      : std_logic;
signal reg_eop_term     : std_logic;
signal sop_occ          : std_logic;
signal soc_occ          : std_logic;
signal term_occ         : std_logic;

signal cnt_crc_placeholder    : std_logic;
signal crc_placeholder_mx     : std_logic_vector(31 downto 0);
signal crc_placeholderisk_mx  : std_logic_vector(3 downto 0);

begin

asfifo_bram_u: asfifo_bram
generic map (
      -- ITEMS = Numer of items in FIFO
      -- !!!!!!!!!!! Must be (2^n)-1, n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS        => 511,

      -- Block Ram Type, only 1, 2, 4, 9, 18, 36 bits
      -- if BRAM_TYPE = 0, best type is automaticaly computed
      BRAM_TYPE    => 36,

      -- Data Width
      DATA_WIDTH   => 36,

      -- Width of status information of fifo fullness
      -- Note=> --,
      --       than ITEMS
      STATUS_WIDTH => 1
   )
   port map(
      RESET       => RESET,

      -- Write interface
      CLK_WR      => CMDCLK,
      WR          => DI_DV,
      DI          => data_to_fifo,
      FULL        => FULL,
      STATUS      => open,

      -- Read interface
      CLK_RD      => USRCLK2,
      RD          => '1',
      DO          => data_from_fifo,
      DO_DV       => data_from_fifo_dv,
      EMPTY       => fifo_empty
   );

cmd_encoder_u0: cmd_encoder
   port map (
      -- Input: command protocol
      DI       => data_from_fifo(7 downto 0),
      DI_CMD   => data_from_fifo(32),

      -- Output=> --,
      DO       => data_to_rio(7 downto 0),
      DOISK    => k_to_rio(0)
   );

cmd_encoder_u1: cmd_encoder
   port map (
      -- Input: command protocol
      DI       => data_from_fifo(15 downto 8),
      DI_CMD   => data_from_fifo(33),

      -- Output=> --,
      DO       => data_to_rio(15 downto 8),
      DOISK    => k_to_rio(1)
   );

cmd_encoder_u2: cmd_encoder
   port map (
      -- Input: command protocol
      DI       => data_from_fifo(23 downto 16),
      DI_CMD   => data_from_fifo(34),

      -- Output=> --,
      DO       => data_to_rio(23 downto 16),
      DOISK    => k_to_rio(2)
   );

cmd_encoder_u3: cmd_encoder
   port map (
      -- Input: command protocol
      DI       => data_from_fifo(31 downto 24),
      DI_CMD   => data_from_fifo(35),

      -- Output=> --,
      DO       => data_to_rio(31 downto 24),
      DOISK    => k_to_rio(3)
   );

   
   -- data bytes must be reordered to satisfy RocketIO requirements
   data_to_fifo <= DI_CMD(0) & DI_CMD(1) & DI_CMD(2) & DI_CMD(3) & 
                   DI(7 downto 0) & DI(15 downto 8) & DI(23 downto 16) & DI(31 downto 24);

   -- When the data from fifo are not ready the IDLE sequence is transmitted instead.
   txdata_i <= data_to_rio when (data_from_fifo_dv = '1') else
             IDLE_PRES & IDLE_PRES;
   txcharisk_i <= k_to_rio when (data_from_fifo_dv = '1') else
                "1010";

   -- EOP logic
   sop_occ <= '1' when (((data_from_fifo(31 downto 24) = C_CMD_SOP) and (data_from_fifo(35) = '1')) or
                        ((data_from_fifo(15 downto 8) = C_CMD_SOP) and (data_from_fifo(33) = '1'))) else
              '0';
              
   soc_occ <= '1' when (((data_from_fifo(31 downto 24) = C_CMD_SOC) and (data_from_fifo(35) = '1')) or
                        ((data_from_fifo(15 downto 8) = C_CMD_SOC) and (data_from_fifo(33) = '1'))) else
              '0';
              
   term_occ <= '1' when ((data_from_fifo(31 downto 24) = C_CMD_TERM) and (data_from_fifo(35) = '1')) or
                        ((data_from_fifo(23 downto 16) = C_CMD_TERM) and (data_from_fifo(34) = '1')) or
                        ((data_from_fifo(15 downto 8) = C_CMD_TERM) and (data_from_fifo(33) = '1')) or
                        ((data_from_fifo(7 downto 0) = C_CMD_TERM) and (data_from_fifo(32) = '1')) else
               '0';
              
-- This register determines if the C_CMD_TERM will signal the end of packet
process(RESET, USRCLK2)
begin
   if (RESET = '1') then
      reg_eop_term <= '0';
   elsif (USRCLK2'event AND USRCLK2 = '1') then
      if (sop_occ = '1') then
         reg_eop_term <= '0';
      elsif (soc_occ = '1') then
         reg_eop_term <= '1';
      end if;
   end if;
end process;

-- End of packet logic. It generates 4 placeholder bytes for CRC end EOP k-char.
reg_eop_set <= term_occ and reg_eop_term and data_from_fifo_dv;

reg_eop_rst <= '1' when cnt_crc_placeholder = '1' else
               '0';

process(RESET, USRCLK2)
begin
   if (RESET = '1') then
      reg_eop <= '0';
   elsif (USRCLK2'event AND USRCLK2 = '1') then
      if (reg_eop_rst = '1') then
         reg_eop <= '0';
      elsif (reg_eop_set = '1') then
         reg_eop <= '1';
      end if;
   end if;
end process;

TXDATA <= crc_placeholder_mx when reg_eop = '1' else
          txdata_i;
TXCHARISK <= crc_placeholderisk_mx when reg_eop = '1' else
             txcharisk_i;

crc_placeholder_mx <= x"00000000" when cnt_crc_placeholder = '0' else
                      K_EOP & K_CEX & IDLE_PRES;
crc_placeholderisk_mx <= "0000" when cnt_crc_placeholder = '0' else
                         "1110";

process(RESET, USRCLK2)
begin
   if (RESET = '1') then
      cnt_crc_placeholder <= '0';
   elsif (USRCLK2'event AND USRCLK2 = '1') then
      if (reg_eop = '1') then
         cnt_crc_placeholder <= not cnt_crc_placeholder;
      end if;
   end if;
end process;

end behavioral;


