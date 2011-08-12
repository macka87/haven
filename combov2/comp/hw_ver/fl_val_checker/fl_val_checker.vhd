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
      RX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;

      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- output interface
      TX_CLK         : in  std_logic;
      TX_RESET       : in  std_logic;

      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUT_DATA_WIDTH/8) - 1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

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

   -- width of the time counter
   constant TIME_CNT_WIDTH : integer := 64;

   -- width of the frame counter
   constant FRAME_CNT_WIDTH : integer := 64;

   constant TIMESTAMP_OFFSET : integer := ERROR_BITMAP_WIDTH;
   constant FRAME_NUM_OFFSET : integer := TIMESTAMP_OFFSET + TIME_CNT_WIDTH;

   -- width of address counter
   constant ADDR_CNT_WIDTH : integer := 2;

   -- width of header
   constant HEADER_WIDTH : integer := 64;

   -- width of the data FIFO
   constant DATA_FIFO_WIDTH : integer := ERROR_BITMAP_WIDTH + TIME_CNT_WIDTH
      + FRAME_CNT_WIDTH;

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
   signal sig_data_fifo_wr_data         : std_logic_vector(DATA_FIFO_WIDTH-1 downto 0);
   signal sig_data_fifo_wr_write        : std_logic;
   
   -- cdc fifo signals read ifc
   signal sig_data_fifo_rd_data   : std_logic_vector(DATA_FIFO_WIDTH-1 downto 0);
   signal sig_data_fifo_rd_read   : std_logic;
   signal sig_data_fifo_rd_almost_empty : std_logic;
   signal sig_data_fifo_rd_empty  : std_logic;

   -- output signals
   signal sig_out_data        : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal sig_out_rem         : std_logic_vector(log2(OUT_DATA_WIDTH/8) - 1 downto 0);
   signal sig_out_src_rdy_n   : std_logic;
   signal sig_out_dst_rdy_n   : std_logic;
   signal sig_out_sof_n       : std_logic;
   signal sig_out_sop_n       : std_logic;
   signal sig_out_eof_n       : std_logic;
   signal sig_out_eop_n       : std_logic;

   -- time counter
   signal time_cnt            : std_logic_vector(TIME_CNT_WIDTH-1 downto 0);

   -- frame counter
   signal frame_cnt           : std_logic_vector(FRAME_CNT_WIDTH-1 downto 0);
   signal frame_cnt_en        : std_logic;

   -- address counter
   signal addr_cnt            : std_logic_vector(ADDR_CNT_WIDTH-1 downto 0);
   signal addr_cnt_en         : std_logic;
   signal addr_cnt_clr        : std_logic;

   signal addr_max            : std_logic;

   -- data
   signal header_data         : std_logic_vector(HEADER_WIDTH-1 downto 0);
   signal timestamp_data      : std_logic_vector(TIME_CNT_WIDTH-1 downto 0);
   signal frame_num_data      : std_logic_vector(FRAME_CNT_WIDTH-1 downto 0);

begin

   -- Assertions
   assert (OUT_DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH"
      severity failure;

   -- FL_VAL_GUARD input
   guard_src_rdy_n  <= RX_SRC_RDY_N;
   guard_dst_rdy_n  <= RX_DST_RDY_N;
   guard_sof_n      <= RX_SOF_N;
   guard_sop_n      <= RX_SOP_N;
   guard_eof_n      <= RX_EOF_N;
   guard_eop_n      <= RX_EOP_N;

   -- --------------- FL_VAL_GUARD INSTANCE -----------------------------------
   fl_val_guard_i : entity work.fl_val_guard
   port map (
      RESET          => RX_RESET,
      CLK            => RX_CLK,

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
   sig_data_fifo_wr_data(ERROR_BITMAP_WIDTH-1 downto 0) <= guard_error_bitmap;
   sig_data_fifo_wr_data(TIMESTAMP_OFFSET+TIME_CNT_WIDTH-1 downto
      TIMESTAMP_OFFSET) <= time_cnt;
   sig_data_fifo_wr_data(FRAME_NUM_OFFSET+FRAME_CNT_WIDTH-1 downto
      FRAME_NUM_OFFSET) <= frame_cnt;
   sig_data_fifo_wr_write <= guard_invalid;

   -- --------------- CDC_FIFO INSTANCE -----------------------------------
   data_fifo_i : entity work.cdc_fifo
   generic map(
      DATA_WIDTH      => DATA_FIFO_WIDTH
   )
   port map(
      RESET           => TX_RESET,
      
      -- Write interface
      WR_CLK          => RX_CLK,
      WR_DATA         => sig_data_fifo_wr_data,
      WR_WRITE        => sig_data_fifo_wr_write,
      WR_FULL         => open,
      WR_ALMOST_FULL  => open,
      
      RD_CLK          => TX_CLK,
      RD_DATA         => sig_data_fifo_rd_data,
      RD_READ         => sig_data_fifo_rd_read,
      RD_EMPTY        => sig_data_fifo_rd_empty,
      RD_ALMOST_EMPTY => sig_data_fifo_rd_almost_empty
   );

   -- ------------------------- Time counter  --------------------------------
   time_cnt_p: process (RX_CLK)
   begin
      if (rising_edge(RX_CLK)) then
         if (RX_RESET = '1') then
            time_cnt <= (others => '0');
         else
            time_cnt <= time_cnt + 1;
         end if;
      end if;
   end process;

   -- ------------------------- Frame counter  -------------------------------
   frame_cnt_en <= NOT (guard_src_rdy_n OR guard_dst_rdy_n OR guard_sof_n);

   -- frame counter
   frame_cnt_p: process (RX_CLK)
   begin
      if (rising_edge(RX_CLK)) then
         if (RX_RESET = '1') then
            frame_cnt <= (others => '0');
         elsif (frame_cnt_en = '1') then
            frame_cnt <= frame_cnt + 1;
         end if;
      end if;
   end process;

   -- ------------------------- Address counter  -----------------------------
   addr_cnt_en  <= NOT (sig_data_fifo_rd_empty OR sig_out_dst_rdy_n);
   addr_cnt_clr <= addr_max;

   -- address counter
   addr_cnt_p: process (TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (TX_RESET = '1') then
            addr_cnt <= (others => '0');
         elsif (addr_cnt_en = '1') then
            if (addr_cnt_clr = '1') then
               addr_cnt <= (others => '0');
            else
               addr_cnt <= addr_cnt + 1;
            end if;
         end if;
      end if;
   end process;

   -- ------------------------- Data multiplexer  -----------------------------
   mux_p: process (header_data, timestamp_data, frame_num_data, addr_cnt)
   begin
      sig_out_data <= header_data;
      sig_out_sof_n <= '1';
      sig_out_sop_n <= '1';
      sig_out_eof_n <= '1';
      sig_out_eop_n <= '1';
      addr_max      <= '0';

      case addr_cnt is
         when "00" => sig_out_data <= header_data;
            sig_out_sof_n <= '0';
            sig_out_sop_n <= '0';

         when "01" => sig_out_data <= timestamp_data;

         when "10" => sig_out_data <= frame_num_data;
            sig_out_eof_n <= '0';
            sig_out_eop_n <= '0';
            addr_max <= '1';
         when others => null;
      end case;

   end process;

   -- create the header word
   header_data(63 downto 48) <=
      sig_data_fifo_rd_data(ERROR_BITMAP_WIDTH-1 downto 0);
   header_data(47 downto 40) <= X"00";
   header_data(39 downto 32) <= INVALID_TRANS_TYPE;
   header_data(31 downto 24) <= X"00";
   header_data(23 downto 16) <= X"00";
   header_data(15 downto  8) <= FL_VAL_CHECKER_PROTOCOL_ID;
   header_data( 7 downto  0) <= ENDPOINT_TAG;

   -- create the timestamp word
   timestamp_data  <= sig_data_fifo_rd_data(TIMESTAMP_OFFSET+TIME_CNT_WIDTH-1
      downto TIMESTAMP_OFFSET);

   -- create the frame number word
   frame_num_data <= sig_data_fifo_rd_data(FRAME_NUM_OFFSET+FRAME_CNT_WIDTH-1
      downto FRAME_NUM_OFFSET);

   -- create the transmitted frame

   sig_out_rem           <= (others => '1');
   sig_out_src_rdy_n     <= sig_data_fifo_rd_empty;
   sig_data_fifo_rd_read <= (NOT sig_out_dst_rdy_n) AND addr_max;

   -- mapping of output ports
   TX_DATA           <= sig_out_data;
   TX_REM            <= sig_out_rem;
   TX_SOP_N          <= sig_out_sop_n;
   TX_EOP_N          <= sig_out_eop_n;
   TX_SOF_N          <= sig_out_sof_n;
   TX_EOF_N          <= sig_out_eof_n;
   TX_SRC_RDY_N      <= sig_out_src_rdy_n;
   sig_out_dst_rdy_n <= TX_DST_RDY_N;

   -- output ready signal
   OUTPUT_READY        <= sig_data_fifo_rd_almost_empty;

end architecture;

