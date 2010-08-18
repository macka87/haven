-- transformer_128to64.vhd: Instance of FrameLink Transformer component.
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FL_TRANSFORMER_128TO64 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- RX interface
      RX_DATA        : in  std_logic_vector(127 downto 0);
      RX_DREM        : in  std_logic_vector(3 downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX interface
      TX_DATA        : out std_logic_vector(63 downto 0);
      TX_DREM        : out std_logic_vector(2 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end entity FL_TRANSFORMER_128TO64;

architecture FULL of FL_TRANSFORMER_128TO64 is

begin

   transformer_i : entity work.fl_transformer
   generic map(
      RX_DATA_WIDTH  => 128,
      TX_DATA_WIDTH  => 64
   )
   port map(
       CLK            => CLK,
       RESET          => RESET,
       --
       RX_DATA        => RX_DATA,
       RX_REM         => RX_DREM,
       RX_SOF_N       => RX_SOF_N,
       RX_EOF_N       => RX_EOF_N,
       RX_SOP_N       => RX_SOP_N,
       RX_EOP_N       => RX_EOP_N,
       RX_SRC_RDY_N   => RX_SRC_RDY_N,
       RX_DST_RDY_N   => RX_DST_RDY_N,
       --
       TX_DATA        => TX_DATA,
       TX_REM         => TX_DREM,
       TX_SOF_N       => TX_SOF_N,
       TX_EOF_N       => TX_EOF_N,
       TX_SOP_N       => TX_SOP_N,
       TX_EOP_N       => TX_EOP_N,
       TX_SRC_RDY_N   => TX_SRC_RDY_N,
       TX_DST_RDY_N   => TX_DST_RDY_N
   );

end architecture FULL;
