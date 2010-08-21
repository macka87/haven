
-- xon_xoff_buffer.vhd: XON/XOFF Buffer
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
use work.aurvc_pkg.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity xon_xoff_buffer is
   port (
      -- Common Interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Input
      ALMOST_FULL       : in std_logic;
      READ              : in std_logic;
      
      -- Output
      XON_XOFF          : out std_logic; 
      EMPTY             : out std_logic

   );
end xon_xoff_buffer;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of xon_xoff_buffer is

component FIFO is
   generic (
      -- Set data width here
      DATA_WIDTH     : integer;

      -- Distributed RAM type, only 16, 32, 64 bits
      DISTMEM_TYPE   : integer := 16;

      -- Set number of items in FIFO here
      ITEMS          : integer;

      -- for last block identification
      BLOCK_SIZE     : integer := 0
   );
   port(
      RESET    : in std_logic;  -- Global reset signal
      CLK      : in std_logic;  -- Global clock signal

      -- Write interface
      DATA_IN  : in std_logic_vector((DATA_WIDTH-1) downto 0); -- Data input
      WRITE_REQ: in std_logic;  -- Write request
      FULL     : out std_logic; -- FIFO is full
      LSTBLK   : out std_logic; -- Last block identifier

      -- Read interface
      DATA_OUT : out std_logic_vector((DATA_WIDTH-1) downto 0); -- Data output
      READ_REQ : in std_logic;  -- Read request
      EMPTY    : out std_logic  -- FIFO is empty
   );
end component;

   signal reg_full      : std_logic;
   signal xon_xoff_in   : std_logic;
   signal write_req     : std_logic;
   signal reg_write_req : std_logic;

begin

process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_full <= '0';
   elsif (CLK'event AND CLK = '1') then
      reg_full <= ALMOST_FULL;
   end if;
end process;

xon_xoff_in <= C_XON when reg_full = '0' else
               C_XOFF;

write_req <= ((not reg_full) and ALMOST_FULL) or (reg_full and (not ALMOST_FULL));

process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_write_req <= '0';
   elsif (CLK'event AND CLK = '1') then
      reg_write_req <= write_req;
   end if;
end process;

fifo_u: FIFO
   generic map(
      -- Set data width here
      DATA_WIDTH     => 1,

      -- Distributed RAM type, only 16, 32, 64 bits
      DISTMEM_TYPE   => 16,

      -- Set number of items in FIFO here
      ITEMS          => 16,

      -- for last block identification
      BLOCK_SIZE     => 1
   )
   port map(
      RESET    => RESET,
      CLK      => CLK,

      -- Write interface
      DATA_IN(0)  => xon_xoff_in,
      WRITE_REQ=> reg_write_req,
      FULL     => open,
      LSTBLK   => open,

      -- Read interface
      DATA_OUT(0) => XON_XOFF,
      READ_REQ => READ,
      EMPTY    => EMPTY
   );

end behavioral;

