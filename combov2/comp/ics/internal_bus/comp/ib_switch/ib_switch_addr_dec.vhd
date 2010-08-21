--
-- ib_switch_addr_dec.vhd: Internal Bus Address decoder
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.ib_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SWITCH_ADDR_DEC is
   generic(
      -- Port 0 Address Space 
      SWITCH_BASE       : std_logic_vector(31 downto 0);
      SWITCH_LIMIT      : std_logic_vector(31 downto 0);
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  : std_logic_vector(31 downto 0);
      DOWNSTREAM0_LIMIT : std_logic_vector(31 downto 0);
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  : std_logic_vector(31 downto 0); 
      DOWNSTREAM1_LIMIT : std_logic_vector(31 downto 0);

      PORT_NO           : integer -- Port number
      );
   port(
      CLK             : in  std_logic;
      RESET           : in  std_logic;
      ADDR_IN         : in  std_logic_vector(31 downto 0);
      TRANS_TYPE      : in  std_logic_vector(C_IB_TRANS_TYPE_WIDTH-1 downto 0);
      IF_SELECT       : out std_logic_vector(2 downto 0);
      MATCH           : out std_logic
      );
end entity IB_SWITCH_ADDR_DEC;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_ADDR_DEC_ARCH of IB_SWITCH_ADDR_DEC is

   signal aux_base0_high   : std_logic_vector(31 downto 0);
   signal aux_base1_high   : std_logic_vector(31 downto 0);
   signal aux_base2_high   : std_logic_vector(31 downto 0);
   signal match_port0      : std_logic;
   signal match_port1      : std_logic;
   signal match_port2      : std_logic;
   signal upstream_sel     : std_logic;
   signal aux_global_trans : std_logic;
   

begin

aux_base0_high   <= SWITCH_BASE      + SWITCH_LIMIT;
aux_base1_high   <= DOWNSTREAM0_BASE + DOWNSTREAM0_LIMIT;
aux_base2_high   <= DOWNSTREAM1_BASE + DOWNSTREAM1_LIMIT;

match_port0      <= '1' when ADDR_IN >= SWITCH_BASE and ADDR_IN < aux_base0_high else '0';
match_port1      <= '1' when ADDR_IN >= DOWNSTREAM0_BASE and ADDR_IN < aux_base1_high else '0';
match_port2      <= '1' when ADDR_IN >= DOWNSTREAM1_BASE and ADDR_IN < aux_base2_high else '0';
-- aux_global_trans <= '1' when (TRANS_TYPE = C_IB_L2GW_TRANSACTION) or (TRANS_TYPE = C_IB_G2LR_TRANSACTION) else '0';
-- Not necessary (thanks to coding we can write
aux_global_trans <= TRANS_TYPE(1);

port0_gen: if (PORT_NO=0) generate
  MATCH     <= (match_port1 or match_port2) and not aux_global_trans;
  IF_SELECT <= match_port2 & match_port1 & '0';
end generate;

port1_gen: if (PORT_NO=1) generate
  MATCH        <= match_port2 or aux_global_trans or not match_port0;
  upstream_sel <= not match_port0 or aux_global_trans;
  IF_SELECT    <= (match_port2 and not upstream_sel) & '0' & upstream_sel;
end generate;

port2_gen: if (PORT_NO=2) generate
  MATCH        <= match_port1 or aux_global_trans or not match_port0;
  upstream_sel <= not match_port0 or aux_global_trans;
  IF_SELECT    <= '0' & (match_port1 and not upstream_sel) & upstream_sel;
end generate;


end architecture IB_SWITCH_ADDR_DEC_ARCH;

