
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
use work.commands.ALL; 
use work.math_pack.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity receiver is
   generic (
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Aurora LocalLink RX interface
      RX_D             : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM           : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N     : in std_logic;
      RX_SOF_N         : in std_logic;
      RX_EOF_N         : in std_logic;
      RX_DST_RDY_N     : out std_logic;

      -- Command protocol interface
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_CMD   : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      DO_DV    : out std_logic; 
      FULL     : in std_logic
   );
end receiver;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of receiver is

component cmd_dec is
   generic(
      NUM_PATHS   : integer := 4
   );
   port(
      -- Input interface
      DI          : in    std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Input Data
      DI_CMD      : in    std_logic_vector((NUM_PATHS-1) downto 0);
      EN          : in    std_logic;

      -- Output interface
      DO          : out   std_logic_vector((NUM_PATHS*8)-1 downto 0); -- Output Data
      CMD_SOP     : out   std_logic;
      CMD_SOC     : out   std_logic;
      CMD_PCKREC  : out   std_logic;
      CMD_IDLE    : out   std_logic;
      CMD_TERM    : out   std_logic;
      CMD_DATA    : out   std_logic;
      LEN         : out   std_logic_vector(log2(NUM_PATHS+1)-1 downto 0)
   );
end component cmd_dec;

   signal cmd_i   : std_logic_vector((DATA_WIDTH/8)-2 downto 0);

begin

-- Coder
--cmd_i(0) <= '1' when (RX_D(7 downto 0) = C_CMD_IDLE) else
--            '0';
cmd_i((DATA_WIDTH/8)-2) <= '1' when (RX_D((DATA_WIDTH)-1 downto (DATA_WIDTH-8)) = C_CMD_IDLE) else
            '0';
term_gen: for i in 1 to (DATA_WIDTH/8)-2 generate
   cmd_i((DATA_WIDTH/8)-2-i) <= '1' when ((cmd_i((DATA_WIDTH/8)-1-i) = '1') and 
                                          (RX_D((((DATA_WIDTH/8)-i)*8)-1 downto ((DATA_WIDTH/8)-i-1)*8) = C_CMD_IDLE)) else
               '0';
end generate;

coder: process(cmd_i, RX_D, RX_SRC_RDY_N, RX_SOF_N, RX_EOF_N)
begin
   DO <= RX_D;
   DO_CMD <= (others => '0');

   if (RX_SOF_N = '0') then
      DO_CMD <= (others => '1');
   end if;

   if (RX_EOF_N = '0') then
      DO_CMD <= '1' & cmd_i;
   end if;
   
end process coder;

DO_DV <= not RX_SRC_RDY_N;
RX_DST_RDY_N <= FULL;

end behavioral;




