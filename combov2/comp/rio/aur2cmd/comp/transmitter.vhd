
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

entity transmitter is
   generic (
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DI       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      DI_CMD   : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      DI_DV    : in std_logic;

      -- Aurora LocalLink TX interface
      TX_D             : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM           : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N     : out std_logic;
      TX_SOF_N         : out std_logic;
      TX_EOF_N         : out std_logic;
      TX_DST_RDY_N     : in std_logic
   );
end transmitter;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of transmitter is

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

component tx_fsm is
   port (
         -- Common Input
         CLK      : in std_logic;
         RESET    : in std_logic;
         
         -- Input
         RDY      : in std_logic;
         CMD_TERM : in std_logic;

         -- Output
         TX_EOF   : out std_logic;
         TX_SOF   : out std_logic
        );
end component;

   signal cmd_idle      : std_logic;
   signal cmd_term      : std_logic;
   signal rdy           : std_logic;

   signal tx_eof        : std_logic;
   signal tx_sof        : std_logic;

begin
cmd_dec_u: cmd_dec
   generic map(
      NUM_PATHS   => (DATA_WIDTH/8)
   )
   port map(
      -- Input interface
      DI          => DI,
      DI_CMD      => DI_CMD,
      EN          => DI_DV,

      -- Output interface
      DO          => open,
      CMD_IDLE    => cmd_idle,
      CMD_TERM    => cmd_term
   );

   TX_D <= DI;

   -- Number of valid bytes in transmitted data (valid for last data beat only - EOF asserted)
   TX_REM <= (others => '1');  -- all bytes are allways valid

   TX_SRC_RDY_N <= not (DI_DV and not cmd_idle);

tx_fsm_u: tx_fsm
   port map(
         -- Common Input
         CLK      => CMDCLK,
         RESET    => RESET,
         
         -- Input
         RDY      => rdy,
         CMD_TERM => cmd_term,

         -- Output
         TX_EOF   => tx_eof,
         TX_SOF   => tx_sof
        );

    rdy <= DI_DV and (not cmd_idle) and (not TX_DST_RDY_N);
    TX_EOF_N <= not tx_eof;
    TX_SOF_N <= not tx_sof;

end behavioral;




