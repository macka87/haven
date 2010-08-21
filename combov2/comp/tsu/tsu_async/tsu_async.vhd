-- tsu_async.vhd: component which makes async ts and ts_dv signal to
--                synchronous.
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tsu_async is
 -- PORTS
 port (
   RESET          : in std_logic;

   -- Input interface
   IN_CLK         : in std_logic;

   IN_TS          : in std_logic_vector(63 downto 0);
   IN_TS_DV       : in std_logic;

   -- Output interface
   OUT_CLK        : in std_logic;

   OUT_TS         : out std_logic_vector(63 downto 0);
   OUT_TS_DV      : out std_logic
 );
end tsu_async;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of tsu_async is

   signal data_empty         : std_logic;
   signal data_full          : std_logic;
   signal data_write         : std_logic;

begin
   ts_data_asfifo : entity work.asfifo
   generic map (
      -- Data Width
      DATA_WIDTH   => 64,
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS        => 4,
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE => 64,

      -- Width of status information of fifo fullness
      -- Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --       than ITEMS
      STATUS_WIDTH => 2
   )
   port map (
      RESET    => RESET,

      -- Write interface
      CLK_WR   => IN_CLK,
      DI       => IN_TS,
      WR       => data_write,
      FULL     => data_full,
      STATUS   => open,

      -- Read interface
      CLK_RD   => OUT_CLK,
      DO       => OUT_TS,
      RD       => '1',
      EMPTY    => data_empty
   );

data_write <= IN_TS_DV and not data_full;

OUT_TS_DV <= '1';
--OUT_TS_DV <= not data_empty;

end architecture behavioral; 
