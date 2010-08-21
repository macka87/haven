--
-- fifo_sync_block_fixedsize.vhd: Synchronous Block FIFO
-- Copyright (C) 2007 CESNET
-- Author(s): Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- FIFO package
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------
entity FIFO_SYNC_BLOCK is
  generic(
    -- type of main FIFO memory
    MAIN_MEM   : mem_type     := BRAM;
    -- type of address FIFO memory (only if block_type = variable_size)
    ADDR_MEM   : mem_type     := LUT;
    LATENCY    : integer      := 1;
    ITEMS      : integer      := 16;
    ITEM_WIDTH : integer      := 32;
    BLOCK_TYPE : block_type   := variable_size;
    BLOCK_SIZE : integer      := 8;
    -- maximum block to be stored (size of address FIFO) - recommended is ITEMS
    MAX_BLOCKS : integer      := 16;
    DISCARD    : discard_type := NoDiscard;
    PREFETCH   : boolean      := false
  );
  port(
    CLK        : in  std_logic;
    RESET      : in  std_logic;

    WR         : in  std_logic;
    DI         : in  std_logic_vector(ITEM_WIDTH-1 downto 0);
    BLK_END    : in  std_logic;
    WR_DISCARD : in  std_logic;

    RD         : in  std_logic;
    DO         : out std_logic_vector(ITEM_WIDTH-1 downto 0);
    DO_DV      : out std_logic;
    BLK_READY  : out std_logic;
    BLK_FINISH : out std_logic;
    RD_DISCARD : in  std_logic;

    FULL       : out std_logic;
    EMPTY      : out std_logic;
    STATUS     : out std_logic_vector(log2(ITEMS) downto 0)
  );
end entity;
