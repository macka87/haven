-- xgmii_strict_mux_ent.vhd : Generic multiplexor for XGMII with 
--                            packet boundaries checking
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

-- --------------------------------------------------------------------
--                         Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

-- Math package - log2 function
use work.math_pack.all;

--+ XGMII Multiplexor that takes care of packet boundaries
entity xgmii_strict_mux is
generic (
   --+ number of XGMII inputs
   XGMII_COUNT  : integer := 4;
   INIT_SEL     : integer := 0
);
port (
   CLK         : in std_logic;
   RESET       : in std_logic;

   --+ information each RX port whether it is between SOP and EOP
   RX_INSIDE_PACKET : in std_logic_vector(XGMII_COUNT - 1 downto 0);

   --+ RX data to multiplex
   XGMII_RXD   : in std_logic_vector(XGMII_COUNT * 64 - 1 downto 0);
   XGMII_RXC   : in std_logic_vector(XGMII_COUNT *  8 - 1 downto 0);
   RX_SOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);
   RX_EOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);

   --+ TX multiplexed output
   XGMII_TXD   : out std_logic_vector(63 downto 0);
   XGMII_TXC   : out std_logic_vector( 7 downto 0);
   TX_SOP      : out std_logic;
   TX_EOP      : out std_logic;

   --+ multiplexor select signal with enable
   SEL_WE      : in std_logic;
   SEL         : in std_logic_vector(log2(XGMII_COUNT) - 1 downto 0);
   SEL_OUT     : out std_logic_vector(log2(XGMII_COUNT) - 1 downto 0)
);
end entity;

