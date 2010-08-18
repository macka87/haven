
-- ad2sd.vhd: Component converting async data to sync

-- !!! IMPORTANT: Input async data MUST be driven by SLOWER clock than
-- !!! the demanded sync output data stream! (ASYNC_CLK < SYNC_CLK)

-- Copyright (C) 2005 CESNET, Liberouter project
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
-- TODO:

library IEEE;
use IEEE.std_logic_1164.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :
-- -------------------------------------------------------------

entity AD2SD is
   generic(
      DATA_WIDTH : integer := 32
   );
   port (
      -- Input
      RESET          : in  std_logic;
      ASYNC_CLK      : in  std_logic;
      SYNC_CLK       : in  std_logic;
      ASYNC_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);

      -- Output
      SYNC_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end AD2SD;

-- -------------------------------------------------------------
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of AD2SD is

signal reg_async_data   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal reg_sync_data    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal cnt_dv           : std_logic;
signal reg_dv           : std_logic;

begin
SYNC_DATA <= reg_sync_data;

process(ASYNC_CLK,RESET)
begin
   if (RESET = '1') then
      reg_async_data <= (others => '0');
   elsif (ASYNC_CLK'event and ASYNC_CLK='1') then
      if (cnt_dv = '0') then
         reg_async_data <= ASYNC_DATA;
      end if;
   end if;
end process;

process(SYNC_CLK,RESET)
begin
   if (RESET = '1') then
      reg_sync_data <= (others => '0');
   elsif (SYNC_CLK'event and SYNC_CLK='1') then
      if (reg_dv = '1') then
         reg_sync_data <= reg_async_data;
      end if;
   end if;
end process;

process(SYNC_CLK,RESET)
begin
   if (RESET = '1') then
      reg_dv <= '0';
   elsif (SYNC_CLK'event and SYNC_CLK='1') then
      reg_dv <= cnt_dv;
   end if;
end process;

process(ASYNC_CLK,RESET)
begin
   if (RESET = '1') then
      cnt_dv <= '0';
   elsif (ASYNC_CLK'event and ASYNC_CLK='1') then
      cnt_dv <= not cnt_dv;
   end if;
end process;

end behavioral;

