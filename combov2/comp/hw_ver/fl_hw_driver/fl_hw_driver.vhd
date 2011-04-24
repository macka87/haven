--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Driver
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity FL_HW_DRIVER is

   generic
   (
      -- data width
      IN_DATA_WIDTH  : integer := 64;
      OUT_DATA_WIDTH : integer := 64
   );

   port
   (
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;

      -- ------------------ ready signal ------------------------------------
      OUTPUT_READY   : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_HW_DRIVER is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

constant DELAY_WIDTH : integer := 9;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- ---- tx_async_fl_unit ----------------------------------------------------
signal tx_async_rx_data          : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_async_rx_rem           : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_async_rx_sof_n         : std_logic;
signal tx_async_rx_eof_n         : std_logic;
signal tx_async_rx_sop_n         : std_logic;
signal tx_async_rx_eop_n         : std_logic;
signal tx_async_rx_src_rdy_n     : std_logic;
signal tx_async_rx_dst_rdy_n     : std_logic;

signal tx_async_rx_delay         : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal tx_async_rx_delay_wr_n    : std_logic;
signal tx_async_rx_delay_rdy_n   : std_logic;
signal tx_async_rx_finish        : std_logic;

signal tx_async_tx_data          : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_async_tx_rem           : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_async_tx_src_rdy_n     : std_logic;
signal tx_async_tx_dst_rdy_n     : std_logic;
signal tx_async_tx_sop_n         : std_logic;
signal tx_async_tx_eop_n         : std_logic;
signal tx_async_tx_sof_n         : std_logic;
signal tx_async_tx_eof_n         : std_logic;

signal tx_async_output_rdy       : std_logic;

-- ---- data fl_fifo ----------------------------------------------------
signal fifo_out_data          : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal fifo_out_rem           : std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
signal fifo_out_src_rdy_n     : std_logic;
signal fifo_out_dst_rdy_n     : std_logic;
signal fifo_out_sop_n         : std_logic;
signal fifo_out_eop_n         : std_logic;
signal fifo_out_sof_n         : std_logic;
signal fifo_out_eof_n         : std_logic;

-- ---- delay fl_fifo ----------------------------------------------------
signal delay_fifo_in_rem            : std_logic_vector(-1 downto 0);

-- ---- fl_driver_ctrl ----------------------------------------------------
signal ctrl_rx_data          : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal ctrl_rx_rem           : std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
signal ctrl_rx_src_rdy_n     : std_logic;
signal ctrl_rx_dst_rdy_n     : std_logic;
signal ctrl_rx_sop_n         : std_logic;
signal ctrl_rx_eop_n         : std_logic;
signal ctrl_rx_sof_n         : std_logic;
signal ctrl_rx_eof_n         : std_logic;

signal ctrl_tx_data          : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal ctrl_tx_rem           : std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
signal ctrl_tx_src_rdy_n     : std_logic;
signal ctrl_tx_dst_rdy_n     : std_logic;
signal ctrl_tx_sop_n         : std_logic;
signal ctrl_tx_eop_n         : std_logic;
signal ctrl_tx_sof_n         : std_logic;
signal ctrl_tx_eof_n         : std_logic;

signal ctrl_tx_delay         : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal ctrl_tx_delay_wr_n    : std_logic;
signal ctrl_tx_delay_rdy_n   : std_logic;

signal ctrl_tx_finish        : std_logic;

begin

   ctrl_rx_data       <= RX_DATA;
   ctrl_rx_rem        <= RX_REM;
   ctrl_rx_src_rdy_n  <= RX_SRC_RDY_N;
   RX_DST_RDY_N       <= ctrl_rx_dst_rdy_n;
   ctrl_rx_sop_n      <= RX_SOP_N;
   ctrl_rx_eop_n      <= RX_EOP_N;
   ctrl_rx_sof_n      <= RX_SOF_N;
   ctrl_rx_eof_n      <= RX_EOF_N;


   -- --------------- FL_DRIVER_CTRL INSTANCE ------------------------------
   fl_driver_ctrl_i : entity work.fl_driver_ctrl
   generic map(
      DATA_WIDTH   => IN_DATA_WIDTH
   )
   port map(
      CLK            => RX_CLK,
      RESET          => RESET,

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        => ctrl_rx_data,
      RX_REM         => ctrl_rx_rem,
      RX_SRC_RDY_N   => ctrl_rx_src_rdy_n,
      RX_DST_RDY_N   => ctrl_rx_dst_rdy_n,
      RX_SOP_N       => ctrl_rx_sop_n,
      RX_EOP_N       => ctrl_rx_eop_n,
      RX_SOF_N       => ctrl_rx_sof_n,
      RX_EOF_N       => ctrl_rx_eof_n,
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        => ctrl_tx_data,
      TX_REM         => ctrl_tx_rem,
      TX_SRC_RDY_N   => ctrl_tx_src_rdy_n,
      TX_DST_RDY_N   => ctrl_tx_dst_rdy_n,
      TX_SOP_N       => ctrl_tx_sop_n,
      TX_EOP_N       => ctrl_tx_eop_n,
      TX_SOF_N       => ctrl_tx_sof_n,
      TX_EOF_N       => ctrl_tx_eof_n,

      TX_DELAY       => ctrl_tx_delay,
      TX_DELAY_WR_N  => ctrl_tx_delay_wr_n,
      TX_DELAY_RDY_N => ctrl_tx_delay_rdy_n,
      
      TX_FINISH      => ctrl_tx_finish
   );

   -- ------------------------------------------------------------------------
   --                         DATA FIFO
   -- ------------------------------------------------------------------------
   data_fifo_i: entity work.fl_fifo
   generic map(
      DATA_WIDTH  => IN_DATA_WIDTH,
      USE_BRAMS   => true,
      ITEMS       => 4096/(IN_DATA_WIDTH/8),
      PARTS       => 1
   )
   port map(
      CLK           => RX_CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => ctrl_tx_data,
      RX_REM        => ctrl_tx_rem,
      RX_SOF_N      => ctrl_tx_sof_n,
      RX_SOP_N      => ctrl_tx_sop_n,
      RX_EOP_N      => ctrl_tx_eop_n,
      RX_EOF_N      => ctrl_tx_eof_n,
      RX_SRC_RDY_N  => ctrl_tx_src_rdy_n, 
      RX_DST_RDY_N  => ctrl_tx_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fifo_out_data,
      TX_REM        => fifo_out_rem,
      TX_SOF_N      => fifo_out_sof_n,
      TX_SOP_N      => fifo_out_sop_n,
      TX_EOP_N      => fifo_out_eop_n,
      TX_EOF_N      => fifo_out_eof_n,
      TX_SRC_RDY_N  => fifo_out_src_rdy_n,
      TX_DST_RDY_N  => fifo_out_dst_rdy_n
   );

   -- ------------------------------------------------------------------------
   --                         DELAY FIFO
   -- ------------------------------------------------------------------------
   delay_fifo_i: entity work.fl_fifo
   generic map(
      DATA_WIDTH  => DELAY_WIDTH-1,
      USE_BRAMS   => false,
      ITEMS       => 4096/(IN_DATA_WIDTH/8),
      PARTS       => 1
   )
   port map(
      CLK           => RX_CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => ctrl_tx_delay(DELAY_WIDTH-2 downto 0),
      RX_REM        => delay_fifo_in_rem,
      RX_SOF_N      => ctrl_tx_delay(DELAY_WIDTH-1),
      RX_SOP_N      => '1',
      RX_EOP_N      => '1',
      RX_EOF_N      => '1',
      RX_SRC_RDY_N  => ctrl_tx_delay_wr_n, 
      RX_DST_RDY_N  => ctrl_tx_delay_rdy_n, 
      
      -- output interface
      TX_DATA       => tx_async_rx_delay(DELAY_WIDTH-2 downto 0),
      TX_REM        => open,
      TX_SOF_N      => tx_async_rx_delay(DELAY_WIDTH-1),
      TX_SOP_N      => open,
      TX_EOP_N      => open,
      TX_EOF_N      => open,
      TX_SRC_RDY_N  => tx_async_rx_delay_wr_n,
      TX_DST_RDY_N  => tx_async_rx_delay_rdy_n
   );

   -- --------------- FL_TRANSFORMER instance -------------------------------
   fl_tran_i : entity work.FL_TRANSFORMER
   generic map(
      RX_DATA_WIDTH      => IN_DATA_WIDTH,
      TX_DATA_WIDTH      => OUT_DATA_WIDTH
   )
   port map(
      CLK             => TX_CLK,
      RESET           => RESET,
      
      -- RX interface
      RX_DATA         => fifo_out_data,
      RX_REM          => fifo_out_rem,
      RX_SOF_N        => fifo_out_sof_n,
      RX_EOF_N        => fifo_out_eof_n,
      RX_SOP_N        => fifo_out_sop_n,
      RX_EOP_N        => fifo_out_eop_n,
      RX_SRC_RDY_N    => fifo_out_src_rdy_n,
      RX_DST_RDY_N    => fifo_out_dst_rdy_n,

      -- TX interface
      TX_DATA         => tx_async_rx_data,
      TX_REM          => tx_async_rx_rem,
      TX_SOF_N        => tx_async_rx_sof_n,
      TX_EOF_N        => tx_async_rx_eof_n,
      TX_SOP_N        => tx_async_rx_sop_n,
      TX_EOP_N        => tx_async_rx_eop_n,
      TX_SRC_RDY_N    => tx_async_rx_src_rdy_n,
      TX_DST_RDY_N    => tx_async_rx_dst_rdy_n
   );

   --tx_async_rx_delay        <= ctrl_tx_delay;
   --tx_async_rx_delay_wr_n   <= ctrl_tx_delay_wr_n;
   --ctrl_tx_delay_rdy_n      <= tx_async_rx_delay_rdy_n;

   tx_async_rx_finish <= ctrl_tx_finish;

   -- --------------- TX_ASYNC_FL_UNIT INSTANCE ------------------------------
   tx_async_fl_unit_i : entity work.tx_async_fl_unit
   generic map(
      DATA_WIDTH   => OUT_DATA_WIDTH
   )
   port map(
      WR_CLK         => RX_CLK,
      RD_CLK         => TX_CLK,
      RESET          => RESET,

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        => tx_async_rx_data,
      RX_REM         => tx_async_rx_rem,
      RX_SRC_RDY_N   => tx_async_rx_src_rdy_n,
      RX_DST_RDY_N   => tx_async_rx_dst_rdy_n,
      RX_SOP_N       => tx_async_rx_sop_n,
      RX_EOP_N       => tx_async_rx_eop_n,
      RX_SOF_N       => tx_async_rx_sof_n,
      RX_EOF_N       => tx_async_rx_eof_n,
      
      -- input delay interface
      RX_DELAY       => tx_async_rx_delay,
      RX_DELAY_WR_N  => tx_async_rx_delay_wr_n,
      RX_DELAY_RDY_N => tx_async_rx_delay_rdy_n,
      
      -- driver is disabled from software
      RX_FINISH      => tx_async_rx_finish,
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        => tx_async_tx_data,
      TX_REM         => tx_async_tx_rem,
      TX_SRC_RDY_N   => tx_async_tx_src_rdy_n,
      TX_DST_RDY_N   => tx_async_tx_dst_rdy_n,
      TX_SOP_N       => tx_async_tx_sop_n,
      TX_EOP_N       => tx_async_tx_eop_n,
      TX_SOF_N       => tx_async_tx_sof_n,
      TX_EOF_N       => tx_async_tx_eof_n,
      
      -- unit is ready 
      OUTPUT_RDY     => tx_async_output_rdy
   );


   TX_DATA        <= tx_async_tx_data;
   TX_REM         <= tx_async_tx_rem;
   TX_SRC_RDY_N   <= tx_async_tx_src_rdy_n;
   tx_async_tx_dst_rdy_n <= TX_DST_RDY_N;
   TX_SOP_N       <= tx_async_tx_sop_n;
   TX_EOP_N       <= tx_async_tx_eop_n;
   TX_SOF_N       <= tx_async_tx_sof_n;
   TX_EOF_N       <= tx_async_tx_eof_n;

   OUTPUT_READY <= tx_async_output_rdy;

end architecture;
