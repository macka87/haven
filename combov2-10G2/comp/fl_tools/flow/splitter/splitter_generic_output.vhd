-- splitter_generic_output.vhd: FrameLink Splitter with generic output width
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
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_SPLITTER_GENERIC_OUTPUT is
   generic(
      -- Input/Output data width - should be multiple of 8
      -- only 8, 16, 32, 64, 128 supported
      DATA_WIDTH     : integer;
      -- number of output interfaces: only 2,4,8,16 supported
      OUTPUT_COUNT   : integer;
      -- Data width of the output interfaces
      OUTPUT_WIDTH   : integer;
      -- number of frame parts
      FRAME_PARTS    : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      
      -- output interface
      TX_SOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(OUTPUT_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector(OUTPUT_COUNT*OUTPUT_WIDTH-1 
                                                                     downto 0);
      TX_REM         : out std_logic_vector(OUTPUT_COUNT*log2(OUTPUT_WIDTH/8)-1 
                                                                     downto 0)
   );
end entity FL_SPLITTER_GENERIC_OUTPUT;


-- ----------------------------------------------------------------------------
--                            Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_SPLITTER_GENERIC_OUTPUT is

   -- ----------------------------------------------------------------------
   --                          Constants
   -- ----------------------------------------------------------------------
   -- FIXED output DREM
   constant DREM_WIDTH    : integer := log2(DATA_WIDTH/8);
   -- Transformed output DREM
   constant TR_DREM_WIDTH : integer := log2(OUTPUT_WIDTH/8);



   -- ----------------------------------------------------------------------
   --                            Signals
   -- ----------------------------------------------------------------------
   signal splitter_tx_sof_n     : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_sop_n     : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_eop_n     : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_eof_n     : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_src_rdy_n : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_dst_rdy_n : std_logic_vector(OUTPUT_COUNT-1 downto 0);
   signal splitter_tx_data      : std_logic_vector(OUTPUT_COUNT*DATA_WIDTH-1 
                                                                    downto 0);
   signal splitter_tx_rem       : std_logic_vector(OUTPUT_COUNT*log2(DATA_WIDTH/8)-1 
                                                                     downto 0);

begin
   FL_SPLITTER_I: entity work.FL_SPLITTER
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      OUTPUT_COUNT   => OUTPUT_COUNT,
      FRAME_PARTS    => FRAME_PARTS
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      RX_SOF_N       => RX_SOF_N,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_EOF_N       => RX_EOF_N,
      RX_SRC_RDY_N   => RX_SRC_RDY_N,
      RX_DST_RDY_N   => RX_DST_RDY_N,
      RX_DATA        => RX_DATA,
      RX_REM         => RX_REM,
      
      -- output interfaces
      TX_SOF_N       => splitter_tx_sof_n,
      TX_SOP_N       => splitter_tx_sop_n,
      TX_EOP_N       => splitter_tx_eop_n,
      TX_EOF_N       => splitter_tx_eof_n,
      TX_SRC_RDY_N   => splitter_tx_src_rdy_n,
      TX_DST_RDY_N   => splitter_tx_dst_rdy_n,
      TX_DATA        => splitter_tx_data,
      TX_REM         => splitter_tx_rem
   ); 


   -- Generate FL_TRANSFORMERS
   gen_transformers: for i in 0 to OUTPUT_COUNT - 1 generate

      OUTPUT_TRANSFORMER_U: entity work.FL_TRANSFORMER
      generic map (
         -- FrameLink data buses width
         -- only 8, 16, 32, 64 and 128 supported
         RX_DATA_WIDTH  => DATA_WIDTH,
         TX_DATA_WIDTH  => OUTPUT_WIDTH
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         -- RX interface
         RX_DATA        => splitter_tx_data((i+1)*DATA_WIDTH - 1 downto
                              i*DATA_WIDTH),
         RX_REM         => splitter_tx_rem((i+1)*DREM_WIDTH - 1 downto
                              i*DREM_WIDTH),
         RX_SOF_N       => splitter_tx_sof_n(i),
         RX_EOF_N       => splitter_tx_eof_n(i),
         RX_SOP_N       => splitter_tx_sop_n(i),
         RX_EOP_N       => splitter_tx_eop_n(i),
         RX_SRC_RDY_N   => splitter_tx_src_rdy_n(i),
         RX_DST_RDY_N   => splitter_tx_dst_rdy_n(i),

         -- TX interface
         TX_DATA        => tx_data((i+1)*OUTPUT_WIDTH - 1 downto
                              i*OUTPUT_WIDTH),
         TX_REM         => tx_rem((i+1)*TR_DREM_WIDTH - 1 downto
                              i*TR_DREM_WIDTH),
         TX_SOF_N       => tx_sof_n(i),
         TX_EOF_N       => tx_eof_n(i),
         TX_SOP_N       => tx_sop_n(i),
         TX_EOP_N       => tx_eop_n(i),
         TX_SRC_RDY_N   => tx_src_rdy_n(i),
         TX_DST_RDY_N   => tx_dst_rdy_n(i)
      );

   end generate;

end architecture full; 

