-- aurfc_4xfl16.vhd: 4x16b FrameLink via AURFC
-- Copyright (C) 2008 CESNET
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
entity aurfc_4xfl16 is
   generic(
      -- insert interface number at the beginning of each frame
      TX_INSERT_IFC     : boolean := true;
      -- remove interface number at the beginning of each frame
      RX_REMOVE_IFC     : boolean := true;
      -- interface number byte offset. The number must be in the FIRST word!!
      RX_IFC_BYTE_OFFSET : integer := 0;
      -- interface number nibble offset: 0 - low; 1 - high
      RX_IFC_NIBBLE_OFFSET : integer := 0;
      -- number of frame parts in TX
      TX_FRAME_PARTS    : integer := 2;
      -- general settings
      DISCARD_BAD_PACKETS : boolean := false;
      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true;
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 3;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 3;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   ); 
   port(
   
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- FrameLink Interface
      TX0            : inout t_fl16;
      TX1            : inout t_fl16;
      TX2            : inout t_fl16;
      TX3            : inout t_fl16;
      RX0            : inout t_fl16;
      RX1            : inout t_fl16;
      RX2            : inout t_fl16;
      RX3            : inout t_fl16;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- Status Interface
      TX_STATUS      : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0);   -- TX fifo status
      RX_STATUS      : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);   -- RX fifo status
      CHANNEL_UP     : out std_logic;
      
      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);
      D_CNT_XON      : out std_logic_vector(31 downto 0);
      D_CNT_XOFF     : out std_logic_vector(31 downto 0);
      D_RX_FULL      : out std_logic_vector(15 downto 0);

      -- MGT Interface
      RXN            : in  std_logic_vector(1 downto 0);
      RXP            : in  std_logic_vector(1 downto 0);
      TXN            : out std_logic_vector(1 downto 0);
      TXP            : out std_logic_vector(1 downto 0);

      -- Chipscope debug interface
      ILA_CONTROL    : inout std_logic_vector(35 downto 0)

   );
end entity aurfc_4xfl16;

architecture full of aurfc_4xfl16 is

   constant DATA_WIDTH : integer := 64;
   signal rx_data             : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal tx_fl64             : t_fl64;
   signal rx_fl64             : t_fl64;

   signal switch_tx0          : t_fl64;
   signal switch_tx0_buffered : t_fl64;
   signal switch_tx0_fl16     : t_fl16;
   signal switch_tx1          : t_fl64;
   signal switch_tx1_buffered : t_fl64;
   signal switch_tx1_fl16     : t_fl16;
   signal switch_tx2          : t_fl64;
   signal switch_tx2_buffered : t_fl64;
   signal switch_tx2_fl16     : t_fl16;
   signal switch_tx3          : t_fl64;
   signal switch_tx3_buffered : t_fl64;
   signal switch_tx3_fl16     : t_fl16;

   signal stamper_rx0         : t_fl16;
   signal stamper_tx0         : t_fl16;
   signal stamper_tx1         : t_fl16;
   signal stamper_tx2         : t_fl16;
   signal stamper_tx3         : t_fl16;

begin
   -- -------------------------------------------------------------------------
   --                       RX -> correct interface
   -- -------------------------------------------------------------------------
   FL_SWITCH_I: entity work.switch_1to4_fl64
      generic map(
         -- Switch informationn byte offset
         IFC_BYTE_OFFSET => RX_IFC_BYTE_OFFSET,
         -- Switch information nibble offset: 0 - low; 1 - high
         IFC_NIBBLE_OFFSET => RX_IFC_NIBBLE_OFFSET
      )
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         -- input interface
         RX             => rx_fl64,
         -- output interfaces
         TX0            => switch_tx0,
         TX1            => switch_tx1,
         TX2            => switch_tx2,
         TX3            => switch_tx3
      );

   FL_FIFO0_I : entity work.FL_FIFO_FL64
      generic map(
         -- True => use BlockBAMs
         -- False => use SelectRAMs
         USE_BRAMS      => true,
         -- number of items in the FIFO
         ITEMS          => 256,  -- one BlockRAM
         -- Size of block (for LSTBLK signal)
         BLOCK_SIZE     => 0,
         -- Width of STATUS signal available
         STATUS_WIDTH   => 1,
         -- Number of parts in each frame
         PARTS          => 2
      )
      port map(
         -- Common signals
         CLK            => CMDCLK,
         RESET          => RESET,
         -- FrameLink interfaces
         RX             => switch_tx0,
         TX             => switch_tx0_buffered,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open,
         FRAME_RDY      => open
      );

   FL_FIFO1_I : entity work.FL_FIFO_FL64
      generic map(
         -- True => use BlockBAMs
         -- False => use SelectRAMs
         USE_BRAMS      => true,
         -- number of items in the FIFO
         ITEMS          => 256,  -- one BlockRAM
         -- Size of block (for LSTBLK signal)
         BLOCK_SIZE     => 0,
         -- Width of STATUS signal available
         STATUS_WIDTH   => 1,
         -- Number of parts in each frame
         PARTS          => 2
      )
      port map(
         -- Common signals
         CLK            => CMDCLK,
         RESET          => RESET,
         -- FrameLink interfaces
         RX             => switch_tx1,
         TX             => switch_tx1_buffered,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open,
         FRAME_RDY      => open
      );

   FL_FIFO2_I : entity work.FL_FIFO_FL64
      generic map(
         -- True => use BlockBAMs
         -- False => use SelectRAMs
         USE_BRAMS      => true,
         -- number of items in the FIFO
         ITEMS          => 256,  -- one BlockRAM
         -- Size of block (for LSTBLK signal)
         BLOCK_SIZE     => 0,
         -- Width of STATUS signal available
         STATUS_WIDTH   => 1,
         -- Number of parts in each frame
         PARTS          => 2
      )
      port map(
         -- Common signals
         CLK            => CMDCLK,
         RESET          => RESET,
         -- FrameLink interfaces
         RX             => switch_tx2,
         TX             => switch_tx2_buffered,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open,
         FRAME_RDY      => open
      );

   FL_FIFO3_I : entity work.FL_FIFO_FL64
      generic map(
         -- True => use BlockBAMs
         -- False => use SelectRAMs
         USE_BRAMS      => true,
         -- number of items in the FIFO
         ITEMS          => 256,  -- one BlockRAM
         -- Size of block (for LSTBLK signal)
         BLOCK_SIZE     => 0,
         -- Width of STATUS signal available
         STATUS_WIDTH   => 1,
         -- Number of parts in each frame
         PARTS          => 2
      )
      port map(
         -- Common signals
         CLK            => CMDCLK,
         RESET          => RESET,
         -- FrameLink interfaces
         RX             => switch_tx3,
         TX             => switch_tx3_buffered,
         -- FIFO state signals
         LSTBLK         => open,
         FULL           => open,
         EMPTY          => open,
         STATUS         => open,
         FRAME_RDY      => open
      );

   FL_TRANSFORMER_TX0_I : entity work.FL_TRANSFORMER_FL64_16
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         RX             => switch_tx0_buffered,
         TX             => switch_tx0_fl16
      );

   FL_TRANSFORMER_TX1_I : entity work.FL_TRANSFORMER_FL64_16
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         RX             => switch_tx1_buffered,
         TX             => switch_tx1_fl16
      );

   FL_TRANSFORMER_TX2_I : entity work.FL_TRANSFORMER_FL64_16
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         RX             => switch_tx2_buffered,
         TX             => switch_tx2_fl16
      );

   FL_TRANSFORMER_TX3_I : entity work.FL_TRANSFORMER_FL64_16
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         RX             => switch_tx3_buffered,
         TX             => switch_tx3_fl16
      );

   GEN_RXSTAMPERS : if RX_REMOVE_IFC generate

      FL_UNSTAMPER0_I : entity work.FL_UNSTAMPER_FL16
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => switch_tx0_fl16,
            TX             => RX0
         );

      FL_UNSTAMPER1_I : entity work.FL_UNSTAMPER_FL16
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => switch_tx1_fl16,
            TX             => RX1
         );

      FL_UNSTAMPER2_I : entity work.FL_UNSTAMPER_FL16
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => switch_tx2_fl16,
            TX             => RX2
         );

      FL_UNSTAMPER3_I : entity work.FL_UNSTAMPER_FL16
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => switch_tx3_fl16,
            TX             => RX3
         );
   end generate;

   GEN_NO_RXSTAMPERS : if not RX_REMOVE_IFC generate
      RX0.SOF_N      <= switch_tx0_fl16.SOF_N;
      RX0.SOP_N      <= switch_tx0_fl16.SOP_N;
      RX0.EOP_N      <= switch_tx0_fl16.EOP_N;
      RX0.EOF_N      <= switch_tx0_fl16.EOF_N;
      RX0.DATA       <= switch_tx0_fl16.DATA;
      RX0.DREM       <= switch_tx0_fl16.DREM;
      RX0.SRC_RDY_N  <= switch_tx0_fl16.SRC_RDY_N;
      switch_tx0_fl16.DST_RDY_N <= RX0.DST_RDY_N;

      RX1.SOF_N      <= switch_tx1_fl16.SOF_N;
      RX1.SOP_N      <= switch_tx1_fl16.SOP_N;
      RX1.EOP_N      <= switch_tx1_fl16.EOP_N;
      RX1.EOF_N      <= switch_tx1_fl16.EOF_N;
      RX1.DATA       <= switch_tx1_fl16.DATA;
      RX1.DREM       <= switch_tx1_fl16.DREM;
      RX1.SRC_RDY_N  <= switch_tx1_fl16.SRC_RDY_N;
      switch_tx1_fl16.DST_RDY_N <= RX1.DST_RDY_N;

      RX2.SOF_N      <= switch_tx2_fl16.SOF_N;
      RX2.SOP_N      <= switch_tx2_fl16.SOP_N;
      RX2.EOP_N      <= switch_tx2_fl16.EOP_N;
      RX2.EOF_N      <= switch_tx2_fl16.EOF_N;
      RX2.DATA       <= switch_tx2_fl16.DATA;
      RX2.DREM       <= switch_tx2_fl16.DREM;
      RX2.SRC_RDY_N  <= switch_tx2_fl16.SRC_RDY_N;
      switch_tx2_fl16.DST_RDY_N <= RX2.DST_RDY_N;

      RX3.SOF_N      <= switch_tx3_fl16.SOF_N;
      RX3.SOP_N      <= switch_tx3_fl16.SOP_N;
      RX3.EOP_N      <= switch_tx3_fl16.EOP_N;
      RX3.EOF_N      <= switch_tx3_fl16.EOF_N;
      RX3.DATA       <= switch_tx3_fl16.DATA;
      RX3.DREM       <= switch_tx3_fl16.DREM;
      RX3.SRC_RDY_N  <= switch_tx3_fl16.SRC_RDY_N;
      switch_tx3_fl16.DST_RDY_N <= RX3.DST_RDY_N;
   end generate;
   

   -- -------------------------------------------------------------------------
   --                            TX interface
   -- -------------------------------------------------------------------------
   GEN_TXSTAMPERS : if TX_INSERT_IFC generate

      stamper_rx0.sof_n    <= TX0.sof_n    ;
      stamper_rx0.eof_n    <= TX0.eof_n    ;
      stamper_rx0.sop_n    <= TX0.sop_n    ;
      stamper_rx0.eop_n    <= TX0.eop_n    ;
      stamper_rx0.src_rdy_n<= TX0.src_rdy_n;
      TX0.dst_rdy_n        <= stamper_rx0.dst_rdy_n;
      stamper_rx0.data     <= TX0.data     ;
      stamper_rx0.drem     <= TX0.drem     ;

      FL_STAMPER0_I : entity work.FL_STAMPER_FL16
         generic map(
            STAMP          => X"0000000000000001"
         )
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => stamper_rx0,
            TX             => stamper_tx0
         );

      FL_STAMPER1_I : entity work.FL_STAMPER_FL16
         generic map(
            STAMP          => X"0000000000000002"
         )
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => TX1,
            TX             => stamper_tx1
         );

      FL_STAMPER2_I : entity work.FL_STAMPER_FL16
         generic map(
            STAMP          => X"0000000000000004"
         )
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => TX2,
            TX             => stamper_tx2
         );

      FL_STAMPER3_I : entity work.FL_STAMPER_FL16
         generic map(
            STAMP          => X"0000000000000008"
         )
         port map(
            CLK            => CMDCLK,
            RESET          => RESET,

            RX             => TX3,
            TX             => stamper_tx3
         );
   end generate;

   GEN_NO_TXSTAMPERS : if not TX_INSERT_IFC generate
      stamper_tx0.SOF_N    <= TX0.SOF_N;
      stamper_tx0.SOP_N    <= TX0.SOP_N;
      stamper_tx0.EOP_N    <= TX0.EOP_N;
      stamper_tx0.EOF_N    <= TX0.EOF_N;
      stamper_tx0.DATA     <= TX0.DATA;
      stamper_tx0.DREM     <= TX0.DREM;
      stamper_tx0.SRC_RDY_N <= TX0.SRC_RDY_N;
      TX0.DST_RDY_N        <= stamper_tx0.DST_RDY_N;

      stamper_tx1.SOF_N    <= TX1.SOF_N;
      stamper_tx1.SOP_N    <= TX1.SOP_N;
      stamper_tx1.EOP_N    <= TX1.EOP_N;
      stamper_tx1.EOF_N    <= TX1.EOF_N;
      stamper_tx1.DATA     <= TX1.DATA;
      stamper_tx1.DREM     <= TX1.DREM;
      stamper_tx1.SRC_RDY_N <= TX1.SRC_RDY_N;
      TX1.DST_RDY_N        <= stamper_tx1.DST_RDY_N;

      stamper_tx2.SOF_N    <= TX2.SOF_N;
      stamper_tx2.SOP_N    <= TX2.SOP_N;
      stamper_tx2.EOP_N    <= TX2.EOP_N;
      stamper_tx2.EOF_N    <= TX2.EOF_N;
      stamper_tx2.DATA     <= TX2.DATA;
      stamper_tx2.DREM     <= TX2.DREM;
      stamper_tx2.SRC_RDY_N <= TX2.SRC_RDY_N;
      TX2.DST_RDY_N        <= stamper_tx2.DST_RDY_N;

      stamper_tx3.SOF_N    <= TX3.SOF_N;
      stamper_tx3.SOP_N    <= TX3.SOP_N;
      stamper_tx3.EOP_N    <= TX3.EOP_N;
      stamper_tx3.EOF_N    <= TX3.EOF_N;
      stamper_tx3.DATA     <= TX3.DATA;
      stamper_tx3.DREM     <= TX3.DREM;
      stamper_tx3.SRC_RDY_N <= TX3.SRC_RDY_N;
      TX3.DST_RDY_N        <= stamper_tx3.DST_RDY_N;
   end generate;

   FL_BINDER_I: entity work.fl_binder_fl16x4to64
      generic map(
         FRAME_PARTS    => TX_FRAME_PARTS,
         SIMPLE_BINDER  => true
      )
      port map(
         CLK            => CMDCLK,
         RESET          => RESET,
         -- input interfaces
         RX0            => stamper_tx0,
         RX1            => stamper_tx1,
         RX2            => stamper_tx2,
         RX3            => stamper_tx3,
         -- output interface
         TX             => tx_fl64
      );
   
   -- -------------------------------------------------------------------------
   -- process to remove X signals in simulations
   process(rx_data)
   begin
      rx_fl64.DATA <= rx_data;
      -- for simulations only:
      -- pragma translate_off 
      for aux in 0 to DATA_WIDTH-1 loop
         if (rx_data(aux) = 'X') then
            rx_fl64.DATA(aux) <= '0';
         else
            rx_fl64.DATA(aux) <= rx_data(aux);
         end if;
      end loop;
      -- pragma translate_on 
   end process; 

   AURFC_FL64_I: entity work.aurfc
   generic map(
      LANES             => 2,
      DATA_PATHS        => DATA_WIDTH/8,
      DISCARD_BAD_PACKETS => DISCARD_BAD_PACKETS,
      RX_IS_HEADER      => RX_IS_HEADER,
      RX_IS_FOOTER      => RX_IS_FOOTER,
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     => TX_FIFO_ITEMS,
      TX_STATUS_WIDTH   => TX_STATUS_WIDTH,
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     => RX_FIFO_ITEMS,
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   => RX_STATUS_WIDTH,
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT,
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK          => LOOPBACK
   )
   port map (
      -- Common Input
      RESET          => reset,
      REFCLK         => refclk,
      USRCLK         => usrclk,
      USRCLK2        => usrclk2,
      CMDCLK         => cmdclk,
      
      -- FrameLink TX Interface
      TX_D             => tx_fl64.DATA,
      TX_REM           => tx_fl64.DREM,
      TX_SRC_RDY_N     => tx_fl64.SRC_RDY_N,
      TX_SOF_N         => tx_fl64.SOF_N,
      TX_SOP_N         => tx_fl64.SOP_N,
      TX_EOF_N         => tx_fl64.EOF_N,
      TX_EOP_N         => tx_fl64.EOP_N,
      TX_DST_RDY_N     => tx_fl64.DST_RDY_N,

      -- FrameLink RX Interface
      RX_D             => rx_data,
      RX_REM           => rx_fl64.DREM,
      RX_SRC_RDY_N     => rx_fl64.SRC_RDY_N,
      RX_SOF_N         => rx_fl64.SOF_N,
      RX_SOP_N         => rx_fl64.SOP_N,
      RX_EOF_N         => rx_fl64.EOF_N,
      RX_EOP_N         => rx_fl64.EOP_N,
      RX_DST_RDY_N     => rx_fl64.DST_RDY_N,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => HARD_ERROR,
      SOFT_ERROR     => SOFT_ERROR,
      FRAME_ERROR    => FRAME_ERROR,

      -- Status Interface
      TX_STATUS      => TX_STATUS,
      RX_STATUS      => RX_STATUS,
      CHANNEL_UP     => CHANNEL_UP,

      -- Debug
      D_STATE        => D_STATE,
      D_CNT_XON   => D_CNT_XON,
      D_CNT_XOFF  => D_CNT_XOFF,
      D_RX_FULL   => D_RX_FULL,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );


end architecture full; 

