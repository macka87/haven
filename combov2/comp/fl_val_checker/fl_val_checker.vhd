--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Validity Checker
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
entity FL_VAL_CHECKER is
   generic
   (
      OUT_DATA_WIDTH : integer := 64;
      ENDPOINT_ID    : integer
   );
   port
   (
      -- probe interface
      PR_CLK         : in  std_logic;
      PR_RESET       : in  std_logic;

      PR_SRC_RDY_N   : in  std_logic;
      PR_DST_RDY_N   : in  std_logic;
      PR_SOP_N       : in  std_logic;
      PR_EOP_N       : in  std_logic;
      PR_SOF_N       : in  std_logic;
      PR_EOF_N       : in  std_logic;
      
      -- output interface
      OUT_CLK        : in  std_logic;
      OUT_RESET      : in  std_logic;

      OUT_DATA       : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      OUT_REM        : out std_logic_vector(log2(OUT_DATA_WIDTH/8) - 1 downto 0);
      OUT_SRC_RDY_N  : out std_logic;
      OUT_DST_RDY_N  : in  std_logic;
      OUT_SOP_N      : out std_logic;
      OUT_EOP_N      : out std_logic;
      OUT_SOF_N      : out std_logic;
      OUT_EOF_N      : out std_logic;

      -- output ready signal
      OUTPUT_READY   : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_VAL_CHECKER is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

   -- width of the bitmap determining errors
   constant ERROR_BITMAP_WIDTH : integer := 16;

   -- FrameLink protocol ID
   constant FL_VAL_CHECKER_PROTOCOL_ID :  std_logic_vector(7 downto 0) := X"10";

   -- transaction type for invalid frame
   constant INVALID_TRANS_TYPE         :  std_logic_vector(7 downto 0) := X"EE";

   -- endpoint tag
   constant ENDPOINT_TAG : std_logic_vector(7 downto 0) :=
      conv_std_logic_vector(ENDPOINT_ID, 8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- probe input signals
   signal guard_src_rdy_n    : std_logic;
   signal guard_dst_rdy_n    : std_logic;
   signal guard_sof_n        : std_logic;
   signal guard_sop_n        : std_logic;
   signal guard_eof_n        : std_logic;
   signal guard_eop_n        : std_logic;

   -- probe output signals
   signal guard_invalid      : std_logic;
   signal guard_error_bitmap : std_logic_vector(ERROR_BITMAP_WIDTH-1 downto 0);

   -- cdc fifo signals write ifc
   signal sig_cdc_fifo_wr_data         : std_logic_vector(ERROR_BITMAP_WIDTH-1 downto 0);
   signal sig_cdc_fifo_wr_write        : std_logic;
   
   -- cdc fifo signals read ifc
   signal sig_cdc_fifo_rd_data   : std_logic_vector(ERROR_BITMAP_WIDTH-1 downto 0);
   signal sig_cdc_fifo_rd_read   : std_logic;
   signal sig_cdc_fifo_rd_almost_empty : std_logic;

   -- output signals
   signal sig_out_data        : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal sig_out_rem         : std_logic_vector(log2(OUT_DATA_WIDTH/8) - 1 downto 0);
   signal sig_out_src_rdy_n   : std_logic;
   signal sig_out_dst_rdy_n   : std_logic;
   signal sig_out_sof_n       : std_logic;
   signal sig_out_sop_n       : std_logic;
   signal sig_out_eof_n       : std_logic;
   signal sig_out_eop_n       : std_logic;

begin

   -- Assertions
   assert (OUT_DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH"
      severity failure;

   -- FL_VAL_GUARD input
   guard_src_rdy_n  <= PR_SRC_RDY_N;
   guard_dst_rdy_n  <= PR_DST_RDY_N;
   guard_sof_n      <= PR_SOF_N;
   guard_sop_n      <= PR_SOP_N;
   guard_eof_n      <= PR_EOF_N;
   guard_eop_n      <= PR_EOP_N;

   -- --------------- FL_VAL_GUARD INSTANCE -----------------------------------
   fl_val_guard_i : entity work.fl_val_guard
   port map (
      RESET          => PR_RESET,
      CLK            => PR_CLK,

      -- Probe interface
      SRC_RDY_N      => guard_src_rdy_n, 
      DST_RDY_N      => guard_dst_rdy_n,
      SOP_N          => guard_sop_n,
      EOP_N          => guard_eop_n,
      SOF_N          => guard_sof_n,
      EOF_N          => guard_eof_n,
     
      -- Report interface
      INVALID        => guard_invalid,
      ERROR_BITMAP   => guard_error_bitmap
   );


   -- CDC FIFO input mapping
   sig_cdc_fifo_wr_data  <= guard_error_bitmap;
   sig_cdc_fifo_wr_write <= guard_invalid;

   -- --------------- CDC_FIFO INSTANCE -----------------------------------
   cdc_fifo_i : entity work.cdc_fifo
   generic map(
      DATA_WIDTH      => ERROR_BITMAP_WIDTH
   )
   port map(
      RESET           => OUT_RESET,
      
      -- Write interface
      WR_CLK          => PR_CLK,
      WR_DATA         => sig_cdc_fifo_wr_data,
      WR_WRITE        => sig_cdc_fifo_wr_write,
      WR_FULL         => open,
      WR_ALMOST_FULL  => open,
      
      RD_CLK          => OUT_CLK,
      RD_DATA         => sig_cdc_fifo_rd_data,
      RD_READ         => sig_cdc_fifo_rd_read,
      RD_EMPTY        => open,
      RD_ALMOST_EMPTY => sig_cdc_fifo_rd_almost_empty
   );


   -- create the transmitted frame
   sig_out_data(63 downto 48)  <= sig_cdc_fifo_rd_data;
   sig_out_data(47 downto 40) <= X"00";
   sig_out_data(39 downto 32) <= INVALID_TRANS_TYPE;
   sig_out_data(31 downto 24) <= X"00";
   sig_out_data(23 downto 16) <= X"00";
   sig_out_data(15 downto  8) <= FL_VAL_CHECKER_PROTOCOL_ID;
   sig_out_data( 7 downto  0) <= ENDPOINT_TAG;

   sig_out_rem           <= (others => '1');
   sig_out_sop_n         <= '0';
   sig_out_eop_n         <= '0';
   sig_out_sof_n         <= '0';
   sig_out_eof_n         <= '0';
   sig_out_src_rdy_n     <= sig_cdc_fifo_rd_almost_empty;
   sig_cdc_fifo_rd_read  <= NOT sig_out_dst_rdy_n;


   -- mapping of output ports
   OUT_DATA           <= sig_out_data;
   OUT_REM            <= sig_out_rem;
   OUT_SOP_N          <= sig_out_sop_n;
   OUT_EOP_N          <= sig_out_eop_n;
   OUT_SOF_N          <= sig_out_sof_n;
   OUT_EOF_N          <= sig_out_eof_n;
   OUT_SRC_RDY_N      <= sig_out_src_rdy_n;
   sig_out_dst_rdy_n  <= OUT_DST_RDY_N;

   -- output ready signal
   OUTPUT_READY        <= sig_cdc_fifo_rd_almost_empty;

end architecture;

