--
-- fl_fork.vhd: Fork component for Frame link
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_FORK is
   generic(
      DATA_WIDTH    : integer:=32;
      OUTPUT_PORTS  : integer:=2;
      -- should there be FIFOs used at outputs?
      USE_FIFOS     : boolean := false;
      -- depth of the FIFOs if present
      FIFO_DEPTH    : integer := 64;
      -- should BlockRAMs be used for FIFOs?
      USE_BRAMS     : boolean := false
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame link input interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;

      -- Frame link concentrated interface
      TX_DATA        : out std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(OUTPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_EOF_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_SOP_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_EOP_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(OUTPUT_PORTS-1 downto 0)
     );
end entity FL_FORK;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_FORK_ARCH of FL_FORK is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant DREM_WIDTH  : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input FrameLink
signal sig_rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_rem        : std_logic_vector(DREM_WIDTH-1 downto 0);
signal sig_rx_sof_n      : std_logic;
signal sig_rx_sop_n      : std_logic;
signal sig_rx_eop_n      : std_logic;
signal sig_rx_eof_n      : std_logic;
signal sig_rx_src_rdy_n  : std_logic;
signal sig_rx_dst_rdy_n  : std_logic;

-- output FrameLinks
signal sig_tx_data       : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal sig_tx_rem        : std_logic_vector(OUTPUT_PORTS*DREM_WIDTH-1 downto 0);
signal sig_tx_sof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal sig_tx_sop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal sig_tx_eop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal sig_tx_eof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal sig_tx_src_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal sig_tx_dst_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);

-- input of FIFOs
signal fifo_rx_data       : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal fifo_rx_rem        : std_logic_vector(OUTPUT_PORTS*DREM_WIDTH-1 downto 0);
signal fifo_rx_sof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_rx_sop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_rx_eop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_rx_eof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_rx_src_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_rx_dst_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);

-- output of FIFOs
signal fifo_tx_data       : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal fifo_tx_rem        : std_logic_vector(OUTPUT_PORTS*DREM_WIDTH-1 downto 0);
signal fifo_tx_sof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_tx_sop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_tx_eop_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_tx_eof_n      : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_tx_src_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal fifo_tx_dst_rdy_n  : std_logic_vector(OUTPUT_PORTS-1 downto 0);

-- misc signals
signal dst_rdy_n_or       : std_logic;
signal shared_src_rdy_n   : std_logic;

begin

   -- mapping input ports
   sig_rx_data          <= RX_DATA;
   sig_rx_rem           <= RX_REM;
   sig_rx_sof_n         <= RX_SOF_N;
   sig_rx_sop_n         <= RX_SOP_N;
   sig_rx_eop_n         <= RX_EOP_N;
   sig_rx_eof_n         <= RX_EOF_N;
   sig_rx_src_rdy_n     <= RX_SRC_RDY_N;
   RX_DST_RDY_N         <= sig_rx_dst_rdy_n;

   -- the OR of DST_RDY_N signals
   dst_rdy_n_or_p: process(fifo_rx_dst_rdy_n)
   begin
      dst_rdy_n_or <= '0';

      for i in 0 to OUTPUT_PORTS-1 loop
         if (fifo_rx_dst_rdy_n(i) = '1') then
            dst_rdy_n_or <= '1';
         end if;
      end loop;
   end process;

   shared_src_rdy_n <= sig_rx_src_rdy_n OR dst_rdy_n_or;
   sig_rx_dst_rdy_n <= dst_rdy_n_or;

   gen_split: for i in 0 to OUTPUT_PORTS-1 generate
     fifo_rx_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)    <= sig_rx_data;
     fifo_rx_rem( (i+1)*DREM_WIDTH-1 downto i*DREM_WIDTH)    <= sig_rx_rem;
     fifo_rx_sof_n(i)                                        <= sig_rx_sof_n;
     fifo_rx_eof_n(i)                                        <= sig_rx_eof_n;
     fifo_rx_sop_n(i)                                        <= sig_rx_sop_n;
     fifo_rx_eop_n(i)                                        <= sig_rx_eop_n;
     fifo_rx_src_rdy_n(i)                                    <= shared_src_rdy_n;
   end generate;

   gen_fifos_true: if (USE_FIFOS) generate
      gen_par_fifos: for i in 0 to OUTPUT_PORTS-1 generate
         fl_fifo_i : entity work.FL_FIFO
         generic map(
            DATA_WIDTH      => DATA_WIDTH,
            ITEMS           => FIFO_DEPTH,
            USE_BRAMS       => USE_BRAMS,
            PARTS           => 1
         )
         port map(
            CLK             => CLK,
            RESET           => RESET,
            
            -- RX interface
            RX_DATA         => fifo_rx_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            RX_REM          => fifo_rx_rem ((i+1)*DREM_WIDTH-1 downto i*DREM_WIDTH),
            RX_SOF_N        => fifo_rx_sof_n(i),
            RX_EOF_N        => fifo_rx_eof_n(i),
            RX_SOP_N        => fifo_rx_sop_n(i),
            RX_EOP_N        => fifo_rx_eop_n(i),
            RX_SRC_RDY_N    => fifo_rx_src_rdy_n(i),
            RX_DST_RDY_N    => fifo_rx_dst_rdy_n(i),

            -- TX interface
            TX_DATA         => fifo_tx_data((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            TX_REM          => fifo_tx_rem ((i+1)*DREM_WIDTH-1 downto i*DREM_WIDTH),
            TX_SOF_N        => fifo_tx_sof_n(i),
            TX_EOF_N        => fifo_tx_eof_n(i),
            TX_SOP_N        => fifo_tx_sop_n(i),
            TX_EOP_N        => fifo_tx_eop_n(i),
            TX_SRC_RDY_N    => fifo_tx_src_rdy_n(i),
            TX_DST_RDY_N    => fifo_tx_dst_rdy_n(i)
         );
      end generate;
   end generate;

   gen_fifos_false: if (NOT USE_FIFOS) generate
      fifo_tx_data             <= fifo_rx_data;
      fifo_tx_rem              <= fifo_rx_rem;
      fifo_tx_sof_n            <= fifo_rx_sof_n;
      fifo_tx_sop_n            <= fifo_rx_sop_n;
      fifo_tx_eop_n            <= fifo_rx_eop_n;
      fifo_tx_eof_n            <= fifo_rx_eof_n;
      fifo_tx_src_rdy_n        <= fifo_rx_src_rdy_n;
      fifo_rx_dst_rdy_n        <= fifo_tx_dst_rdy_n;
   end generate;

   -- creating the output FrameLink
   sig_tx_data         <= fifo_tx_data;
   sig_tx_rem          <= fifo_tx_rem;
   sig_tx_sof_n        <= fifo_tx_sof_n;
   sig_tx_sop_n        <= fifo_tx_sop_n;
   sig_tx_eop_n        <= fifo_tx_eop_n;
   sig_tx_eof_n        <= fifo_tx_eof_n;
   sig_tx_src_rdy_n    <= fifo_tx_src_rdy_n;
   fifo_tx_dst_rdy_n   <= sig_tx_dst_rdy_n;

   -- mapping output ports
   TX_DATA             <= sig_tx_data;
   TX_REM              <= sig_tx_rem;
   TX_SOF_N            <= sig_tx_sof_n;
   TX_SOP_N            <= sig_tx_sop_n;
   TX_EOP_N            <= sig_tx_eop_n;
   TX_EOF_N            <= sig_tx_eof_n;
   TX_SRC_RDY_N        <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n    <= TX_DST_RDY_N;

end architecture FL_FORK_ARCH;
