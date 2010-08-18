-- crossbar.vhd: Binder crossbar
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_CROSSBAR is
   generic(
      DATA_WIDTH     : integer;
      COUNT          : integer  -- total count of input interfaces
   );
   port(
      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(COUNT*DATA_WIDTH-1 
                           downto 0);
      RX_REM         : in  std_logic_vector(COUNT*log2(DATA_WIDTH/8)-1 
                           downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      -- control signals
      IFC            : in  std_logic_vector(log2(COUNT)-1 downto 0)
   );
end entity FLB_CROSSBAR;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_CROSSBAR is
   -- ------------------ Signals declaration ----------------------------------
   
begin
   -- ------------------ Directly mapped signals ------------------------------
   -- SOF_N multiplexer
   MX_SOF_N : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_SOF_N,
         SEL         => IFC,
         DATA_OUT(0) => TX_SOF_N
      );

   -- SOP_N multiplexer
   MX_SOP_N : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_SOP_N,
         SEL         => IFC,
         DATA_OUT(0) => TX_SOP_N
      );

   -- EOP_N multiplexer
   MX_EOP_N : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_EOP_N,
         SEL         => IFC,
         DATA_OUT(0) => TX_EOP_N
      );

   -- EOF_N multiplexer
   MX_EOF_N : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_EOF_N,
         SEL         => IFC,
         DATA_OUT(0) => TX_EOF_N
      );

   -- SRC_RDY multiplexer
   MX_SRC_RDY_N : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 1,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_SRC_RDY_N,
         SEL         => IFC,
         DATA_OUT(0) => TX_SRC_RDY_N
      );

   -- DST_RDY demultiplexer
   DMX_DST_RDY_N : entity work.GEN_DEMUX
      generic map(
         DATA_WIDTH  => 1,
         DEMUX_WIDTH => COUNT,
         DEF_VALUE   => '1'
      )
      port map(
         DATA_IN(0)  => TX_DST_RDY_N,
         SEL         => IFC,
         DATA_OUT    => RX_DST_RDY_N
      );
   
   -- DATA multiplexer
   MX_DATA : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => DATA_WIDTH,
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_DATA,
         SEL         => IFC,
         DATA_OUT    => TX_DATA
      );

   -- REM multiplexer
   MX_REM : entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => log2(DATA_WIDTH/8),
         MUX_WIDTH   => COUNT
      )
      port map(
         DATA_IN     => RX_REM,
         SEL         => IFC,
         DATA_OUT    => TX_REM
      );

end architecture full;
