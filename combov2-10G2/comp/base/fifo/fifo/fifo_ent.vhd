--
-- fifo.vhd: FIFO - m x n bit
--                - synchronous write, asynchronous read
-- Copyright (C) 2003 CESNET
-- Author(s):  Pecenka Tomas pecenka@liberouter.org
--             Pus Viktor    pus@liberouter.org
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
use work.math_pack.all;

-- auxilary functions and constant needed to evaluate generic address etc.
use WORK.distmem_func.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FIFO is
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
end entity FIFO;
