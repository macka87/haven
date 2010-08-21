-- tx_out_array.vhd: Array of TX_OUT units.
-- Copyright (C) 2004 CESNET
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


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

entity tx_out_array is
generic (
   TX_COUNT    : integer := 4;
   DATA_WIDTH  : integer := 32
);
port (
   CLK         : in  std_logic;
   RESET       : in  std_logic;
   IFNUM       : in  std_logic_vector(TX_COUNT - 1 downto 0);
   SEND_EN_N   : in  std_logic;
   RELOAD      : out std_logic;

   TX_SRC_RDY_N   : out std_logic_vector(TX_COUNT - 1 downto 0);
   TX_DST_RDY_N   : in  std_logic_vector(TX_COUNT - 1 downto 0)
);
end entity;

architecture full of tx_out_array is

   signal tx_out_reload : std_logic;
   signal tx_out_src_rdy_n : std_logic_vector(TX_COUNT - 1 downto 0);
   signal tx_out_dst_rdy_n : std_logic_vector(TX_COUNT - 1 downto 0);

begin

   RELOAD            <= tx_out_reload;
   TX_SRC_RDY_N      <= tx_out_src_rdy_n;
   tx_out_dst_rdy_n  <= TX_DST_RDY_N;

   -- for each TX INTERFACE add one tx_out unit, that solves SRC_RDY/DST_RDY problems
   gen_tx_out_array : 
   for i in 0 to TX_COUNT - 1 generate
      gen_tx_out_unit : entity work.tx_out
      port map (
         CLK   => CLK,
         RESET => RESET,
         IFNUM => IFNUM(i),
         EN_N  => SEND_EN_N,
         RELOAD => tx_out_reload,
         
         TX_SRC_RDY_N => tx_out_src_rdy_n(i),
         TX_DST_RDY_N => tx_out_dst_rdy_n(i)
      );
   end generate;


   --
   -- RELOAD signal
   --

   reload_and_gate : process(tx_out_src_rdy_n)
      variable var_reload : std_logic := '1';
   begin
     
      -- when all tx_out sets src_rdy_n to '1', we can reload them
      -- (so let's constract a big AND gate over all tx_out_src_rdy_n)
      for i in 0 to TX_COUNT - 1 loop
         var_reload := var_reload and tx_out_src_rdy_n(i);
      end loop;

      tx_out_reload <= var_reload;
   end process;

end architecture;


