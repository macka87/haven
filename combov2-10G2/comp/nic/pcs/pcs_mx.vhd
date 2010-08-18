--
-- pcs_mx.vhd: PCS MX
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity pcs_mx is
   port(
      -- Global signals
      RESET    : in  std_logic;

      -- 8/10 interface
      RX_LOST  : in  std_logic;
      RX_D10   : in  std_logic_vector(9 downto 0);
      RX_LSTAT : out std_logic;
      TX_D10   : out std_logic_vector(9 downto 0);

      -- GMII interface
      RX_CLK   : in  std_logic;
      RX_D     : out std_logic_vector(7 downto 0);
      RX_DV    : out std_logic;
      RX_ER    : out std_logic;

      TX_CLK   : in  std_logic;
      TX_D     : in  std_logic_vector(7 downto 0);
      TX_EN    : in  std_logic;
      TX_ER    : in  std_logic
   );
end entity pcs_mx;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of pcs_mx is

begin

-- pcs in component instantion
PCSIN_U : entity work.pcs_mx_in
port map(
   RESET	   => RESET,

   RX_CLK	=> RX_CLK,
   RXLOST	=> RX_LOST,
   DATA_10	=> RX_D10,

   RX_D	   => RX_D,
   RX_DV	   => RX_DV,
   RX_ERR	=> RX_ER,
   LSTAT    => RX_LSTAT
);

-- pcs out component instantion
PCSOUT_U : entity work.pcs_mx_out
port map(
   RESET     => RESET,
   DATA_10   => TX_D10,

   TX_CLK    => TX_CLK,
   TX_D      => TX_D,
   TX_EN     => TX_EN,
   TX_ERR    => TX_ER
);

end architecture behavioral;

