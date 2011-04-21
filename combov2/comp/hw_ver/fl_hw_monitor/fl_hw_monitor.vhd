--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Monitor
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
entity FL_HW_MONITOR is

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
   
end entity FL_HW_MONITOR;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_HW_MONITOR is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant DATA_FIFO_WIDTH : integer := IN_DATA_WIDTH + log2(IN_DATA_WIDTH/8) + 4;

constant REM_INDEX  : integer := 4+log2(OUT_DATA_WIDTH/8);

constant LFSR_GENERATOR_SEED : std_logic_vector(7 downto 0) := "10011011";

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- data fifo signals
signal sig_data_fifo_wr_data         : std_logic_vector(DATA_FIFO_WIDTH-1 downto 0);
signal sig_data_fifo_wr_write        : std_logic;
signal sig_data_fifo_wr_almost_full  : std_logic;
signal sig_data_fifo_wr_full         : std_logic;

signal sig_data_fifo_rd_data   : std_logic_vector(DATA_FIFO_WIDTH-1 downto 0);
signal sig_data_fifo_rd_read   : std_logic;
signal sig_data_fifo_rd_empty  : std_logic;

-- LFSR signals
signal lfsr_output       : std_logic;


begin

   assert (IN_DATA_WIDTH = OUT_DATA_WIDTH)
      report "IN_DATA_WIDTH must be equal to OUT_DATA_WIDTH"
      severity failure;


   -- Mapping of input and output ports
   TX_DATA                <= sig_data_fifo_rd_data(DATA_FIFO_WIDTH-1 downto REM_INDEX);
   TX_REM                 <= sig_data_fifo_rd_data(REM_INDEX-1 downto 4);
   TX_SOF_N               <= sig_data_fifo_rd_data(0);
   TX_SOP_N               <= sig_data_fifo_rd_data(1); 
   TX_EOF_N               <= sig_data_fifo_rd_data(2);
   TX_EOP_N               <= sig_data_fifo_rd_data(3);
   TX_SRC_RDY_N           <= sig_data_fifo_rd_empty;
   sig_data_fifo_rd_read  <= not TX_DST_RDY_N;

   sig_data_fifo_wr_data(DATA_FIFO_WIDTH-1 downto REM_INDEX)  <= RX_DATA;
   sig_data_fifo_wr_data(REM_INDEX-1 downto 4)                <= RX_REM;
   sig_data_fifo_wr_data(0)  <= RX_SOF_N;
   sig_data_fifo_wr_data(1)  <= RX_SOP_N;
   sig_data_fifo_wr_data(2)  <= RX_EOF_N;
   sig_data_fifo_wr_data(3)  <= RX_EOP_N;
   sig_data_fifo_wr_write    <= not (RX_SRC_RDY_N or lfsr_output);
   RX_DST_RDY_N              <= lfsr_output OR sig_data_fifo_wr_full;

   OUTPUT_READY        <= not sig_data_fifo_wr_almost_full;

   -- --------------- DATA FIFO INSTANCE ------------------------------------
   data_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH  => DATA_FIFO_WIDTH
   )
   port map(
      RESET       => RESET,
      
      -- Write interface
      WR_CLK          => RX_CLK,
      WR_DATA         => sig_data_fifo_wr_data,
      WR_WRITE        => sig_data_fifo_wr_write,
      WR_FULL         => sig_data_fifo_wr_full,
      WR_ALMOST_FULL  => sig_data_fifo_wr_almost_full,
      
      RD_CLK          => TX_CLK,
      RD_DATA         => sig_data_fifo_rd_data,
      RD_READ         => sig_data_fifo_rd_read,
      RD_EMPTY        => sig_data_fifo_rd_empty,
      RD_ALMOST_EMPTY => open
   );


   -- --------------- LFSR RANDOM BITSTREAM GENERATOR INSTANCE --------------
   lfsr : entity work.prng_8
   port map(
      CLK     => RX_CLK,
      RESET   => RESET,
      SEED    => LFSR_GENERATOR_SEED,
      OUTPUT  => lfsr_output
   );



end architecture;
