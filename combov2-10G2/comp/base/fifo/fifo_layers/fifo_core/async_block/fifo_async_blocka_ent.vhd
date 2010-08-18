--
-- fifo_async_blocka_ent.vhd: Asynchronous block FIFO
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.fifo_pkg.all;
--For Log2
use work.math_pack.all;
use work.cnt_types.all;

entity FIFO_ASYNC_BLOCKA is
   generic(
      discard : discard_type := WriteDiscard;
      mem_type : mem_type:= LUT;
      latency : integer := 1;
      items : integer := 10;
      item_width : integer := 32;
      block_type : block_type := fixed_size;
      block_size : integer := 5;
      prefetch : boolean := false
   );
   port (
      RESET : in std_logic;
      WR_CLK : in std_logic;
      WR : in std_logic;
      DI : in std_logic_vector(item_width-1 downto 0);
      BLK_END : in std_logic;
      WR_DISCARD : in std_logic;

      RD_CLK : in std_logic;
      RD : in std_logic;
      DO : out std_logic_vector(item_width-1 downto 0);
      DO_DV : out std_logic;
      RD_DISCARD : in std_logic;
      BLK_READY: out std_logic;
      BLK_FINISH : out std_logic;

      EMPTY : out std_logic;
      FULL : out std_logic;
      STATUS : out std_logic_vector(log2(items)-1 downto 0)
      
   );
end entity;
