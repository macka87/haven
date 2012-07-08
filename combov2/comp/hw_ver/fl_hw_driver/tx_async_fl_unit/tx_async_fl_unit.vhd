-- --------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    TX Asynchronous FrameLink Unit  
-- Description: 
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         15.4.2011 (update 20.4.2012)
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity TX_ASYNC_FL_UNIT is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      DELAY_WIDTH    : integer := 9
   );

   port
   (
      WR_CLK         : in  std_logic;
      RD_CLK         : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- input delay interface
      RX_DELAY       : in  std_logic_vector(DELAY_WIDTH-1 downto 0);
      RX_DELAY_WR_N  : in  std_logic;
      RX_DELAY_RDY_N : out std_logic;
      
      -- driver is disabled from software
      RX_FINISH      : in  std_logic; 
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      
      -- unit is ready 
      OUTPUT_RDY     : out std_logic
      
   );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of TX_ASYNC_FL_UNIT is
-- ==========================================================================
--                                      TYPES
-- ==========================================================================


-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
constant FIFO_DATA_WIDTH : integer := DATA_WIDTH + log2(DATA_WIDTH/8) + 4;
constant REM_INDEX  : integer := 4+log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- data fifo signals
signal sig_data_fifo_write      : std_logic;
signal sig_data_fifo_data_in    : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_data_out   : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_read       : std_logic;
signal sig_data_fifo_empty      : std_logic;
signal sig_data_fifo_almost_full: std_logic;

-- delay fifo signals
signal sig_delay_fifo_write       : std_logic;
signal sig_delay_fifo_data        : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal sig_delay_fifo_read        : std_logic;
signal sig_delay_fifo_empty       : std_logic;
signal sig_delay_fifo_almost_full : std_logic;

signal sig_dst_rdy                : std_logic;
signal sig_src_rdy                : std_logic;
signal sig_output_rdy             : std_logic;

-- the delay unit
signal delay_unit_delay_data      : std_logic_vector(DELAY_WIDTH-1 downto 0);
signal delay_unit_delay_empty     : std_logic;
signal delay_unit_delay_read      : std_logic;
signal delay_unit_src_rdy         : std_logic;
signal delay_unit_dst_rdy         : std_logic;
   

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   sig_data_fifo_data_in(FIFO_DATA_WIDTH-1 downto REM_INDEX) <= RX_DATA;
   sig_data_fifo_data_in(REM_INDEX-1 downto 4)               <= RX_REM;
   sig_data_fifo_data_in(0)                                  <= RX_SOF_N;
   sig_data_fifo_data_in(1)                                  <= RX_EOF_N;
   sig_data_fifo_data_in(2)                                  <= RX_SOP_N;
   sig_data_fifo_data_in(3)                                  <= RX_EOP_N;

   -- --------------- DATA FIFO INSTANCE ------------------------------------
   data_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH  => FIFO_DATA_WIDTH
   )
   port map(
      RESET       => RESET,
      
      -- Write interface
      WR_CLK          => WR_CLK,
      WR_DATA         => sig_data_fifo_data_in,
      WR_WRITE        => sig_data_fifo_write,
      WR_FULL         => RX_DST_RDY_N,
      WR_ALMOST_FULL  => sig_data_fifo_almost_full,
      
      RD_CLK          => RD_CLK,
      RD_DATA         => sig_data_fifo_data_out,
      RD_READ         => sig_data_fifo_read,
      RD_EMPTY        => sig_data_fifo_empty,
      RD_ALMOST_EMPTY => open --sig_data_fifo_rdy
   );
   
   -- --------------- DELAY FIFO INSTANCE -----------------------------------
   delay_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH  => DELAY_WIDTH
   )
   port map(
      RESET       => RESET,
      
      -- Write interface
      WR_CLK          => WR_CLK,
      WR_DATA         => RX_DELAY,
      WR_WRITE        => sig_delay_fifo_write,
      WR_FULL         => RX_DELAY_RDY_N,
      WR_ALMOST_FULL  => sig_delay_fifo_almost_full,
      
      RD_CLK          => RD_CLK,
      RD_DATA         => sig_delay_fifo_data,
      RD_READ         => sig_delay_fifo_read,
      RD_EMPTY        => sig_delay_fifo_empty,
      RD_ALMOST_EMPTY => open --sig_delay_fifo_rdy
   );

   -- ================= IMPLEMENTATION ======================================
   
   -- ----- data fifo input side -----
   sig_data_fifo_write  <= not RX_SRC_RDY_N;
   
   -- ----- data fifo output side -----
   TX_SOF_N <= sig_data_fifo_data_out(0);
   TX_EOF_N <= sig_data_fifo_data_out(1);
   TX_SOP_N <= sig_data_fifo_data_out(2);
   TX_EOP_N <= sig_data_fifo_data_out(3);
   TX_REM   <= sig_data_fifo_data_out(REM_INDEX-1 downto 4); 
   TX_DATA  <= sig_data_fifo_data_out(FIFO_DATA_WIDTH-1 downto REM_INDEX);
   
   sig_data_fifo_read <= sig_dst_rdy and sig_src_rdy;
   
   -- ----- delay fifo input side -----
   sig_delay_fifo_write <= not RX_DELAY_WR_N;
   
   --
   delay_unit_delay_data  <= sig_delay_fifo_data;
   delay_unit_delay_empty <= sig_delay_fifo_empty OR sig_data_fifo_empty;
   sig_delay_fifo_read    <= delay_unit_delay_read;

   -- --------------- TX DELAY PROC UNIT INSTANCE ---------------------------
   delay_unit_i : entity work.tx_delay_proc_unit
   generic map(
      DELAY_WIDTH  => DELAY_WIDTH
   )
   port map(
      CLK            => RD_CLK,
      RESET          => RESET,

      -- input
      DELAY_DATA     => delay_unit_delay_data,
      DELAY_EMPTY    => delay_unit_delay_empty,
      DELAY_READ     => delay_unit_delay_read,

      -- output
      DST_RDY        => delay_unit_dst_rdy,
      SRC_RDY        => delay_unit_src_rdy
   );

   delay_unit_dst_rdy <= sig_dst_rdy;
   sig_src_rdy        <= delay_unit_src_rdy;
   
   --
   sig_output_rdy <= RX_FINISH or (sig_data_fifo_almost_full and 
                                   sig_delay_fifo_almost_full);
                                   
   -- mapping outputs
   OUTPUT_RDY   <= sig_output_rdy;
   TX_SRC_RDY_N <= not sig_src_rdy;
   sig_dst_rdy  <= not TX_DST_RDY_N;
   
       
end architecture;
