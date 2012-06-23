-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    fl_cov_unit.vhd
-- Description:  Unit for checking FrameLink functional coverage
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         6.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- this unit checks functional coverage of FrameLink and sends the coverage
-- periodically to SW using FrameLink frames
entity fl_cov_unit is

   generic
   (
      -- input FrameLink data width
      IN_DATA_WIDTH  : integer := 64;
      -- output FrameLink data width
      OUT_DATA_WIDTH : integer := 64;
      -- the interval between sending coverage report to SW
      SEND_INTERVAL  : integer := 1024;
      ENDPOINT_ID    : integer := 64
   );

   port
   (
      RX_CLK         :  in std_logic;
      RX_RESET       :  in std_logic;
      TX_CLK         :  in std_logic;
      TX_RESET       :  in std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface (without the data signal, it is not important)
      RX_REM         :  in std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N       :  in std_logic;
      RX_EOP_N       :  in std_logic;
      RX_SOF_N       :  in std_logic;
      RX_EOF_N       :  in std_logic;
      RX_SRC_RDY_N   :  in std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

      -- ------------------ ready signal ------------------------------------
      OUTPUT_READY   : out std_logic
   );

end entity;


-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of fl_cov_unit is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- number of states of the state space of control signals
constant CONTROL_NUM_STATES      : integer := 0
           -- | SOF_N | EOF_N | SOP_N | EOP_N |
  + 1      -- |   0   |   0   |   0   |   0   |
  + 1      -- |   0   |   1   |   0   |   0   |
  + 1      -- |   0   |   1   |   0   |   1   |
  + 1      -- |   1   |   0   |   0   |   0   |
  + 1      -- |   1   |   0   |   1   |   0   |
  + 1      -- |   1   |   1   |   0   |   0   |
  + 1      -- |   1   |   1   |   0   |   1   |
  + 1      -- |   1   |   1   |   1   |   0   |
  + 1      -- |   1   |   1   |   1   |   1   |
;

-- the number of data frames at the output
constant CONTROL_FRAME_LENGTH    : integer := ((CONTROL_NUM_STATES-1) / OUT_DATA_WIDTH) + 1;

-- the width of the DREM signal
constant IN_DREM_WIDTH     : integer := log2(IN_DATA_WIDTH/8);

-- the number of possible values in input DREM
constant IN_DREM_NUM       : integer := 2**IN_DREM_WIDTH;

-- real input width (DREM + 4 control signals)
constant REAL_IN_WIDTH     : integer := IN_DREM_WIDTH + 4;

constant TOTAL_STATE_SPACE_SIZE : integer := 16 + IN_DREM_NUM;

constant FRAME_LENGTH      : integer := 1;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- data fifo signals write ifc
signal sig_data_fifo_wr_data         : std_logic_vector(REAL_IN_WIDTH-1 downto 0);
signal sig_data_fifo_wr_write        : std_logic;

-- data fifo signals read ifc
signal sig_data_fifo_rd_data         : std_logic_vector(REAL_IN_WIDTH-1 downto 0);
signal sig_data_fifo_rd_read         : std_logic;
signal sig_data_fifo_rd_empty        : std_logic;
signal sig_data_fifo_rd_almost_empty : std_logic;

-- FrameLink signals extracted from FIFO output
signal sig_sof_n               : std_logic;
signal sig_eof_n               : std_logic;
signal sig_sop_n               : std_logic;
signal sig_eop_n               : std_logic;
signal sig_rem                 : std_logic_vector(IN_DREM_WIDTH-1 downto 0);

-- coverage registers
signal sig_coverage_regs_en    : std_logic;
signal reg_controls            : std_logic_vector(CONTROL_NUM_STATES-1 downto 0);
signal sig_reg_controls_in     : std_logic_vector(CONTROL_NUM_STATES-1 downto 0);
signal reg_drem                : std_logic_vector(IN_DREM_NUM-1 downto 0);
signal sig_reg_drem_in         : std_logic_vector(IN_DREM_NUM-1 downto 0);

-- control rearranger input
signal rx_rearranger_data      : std_logic_vector(TOTAL_STATE_SPACE_SIZE-1 downto 0);
signal rx_rearranger_valid     : std_logic;
signal rx_rearranger_read_next : std_logic;

-- control rearranger output
signal tx_rearranger_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_rearranger_valid     : std_logic;
signal tx_rearranger_read_next : std_logic;

-- the control sample signal
signal sig_sample            : std_logic;

-- the register that samples control state space before sending it
signal reg_sample            : std_logic_vector(CONTROL_NUM_STATES+IN_DREM_NUM-1 downto 0);
signal reg_sample_in         : std_logic_vector(CONTROL_NUM_STATES+IN_DREM_NUM-1 downto 0);
signal reg_sample_en         : std_logic;

-- the register that denotes whether the data in the control sample register is valid
signal reg_sample_valid_reg     : std_logic;
signal reg_sample_valid_reg_set : std_logic;
signal reg_sample_valid_reg_clr : std_logic;

-- the register that denotes whether the rearranger has completed sending a frame
signal reg_rearranger_completed      : std_logic;
signal reg_rearranger_completed_clr  : std_logic;
signal reg_rearranger_completed_set  : std_logic;

-- the acc_time_counter counting the interval between sending of coverage report packets
signal acc_time_counter              : std_logic_vector(log2(SEND_INTERVAL-1) downto 0);
signal acc_time_counter_en           : std_logic;
signal acc_time_counter_clr          : std_logic;

-- the comparer of acc_time_counter
signal cmp_acc_time_counter_is_max_in: std_logic_vector(log2(SEND_INTERVAL-1) downto 0);
signal cmp_acc_time_counter_is_max   : std_logic;

-- packetizer input
signal rx_packetizer_data            : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal rx_packetizer_valid           : std_logic;
signal rx_packetizer_read_next       : std_logic;

-- packetizer output
signal tx_packetizer_data            : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_packetizer_rem             : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_packetizer_sof_n           : std_logic;
signal tx_packetizer_sop_n           : std_logic;
signal tx_packetizer_eof_n           : std_logic;
signal tx_packetizer_eop_n           : std_logic;
signal tx_packetizer_src_rdy_n       : std_logic;
signal tx_packetizer_dst_rdy_n       : std_logic;

begin

   -- Assertions
   assert (OUT_DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH!"
      severity failure;

   -- --------------- MAPPING OF INPUT PORTS --------------------------------
   sig_data_fifo_wr_write  <= not (RX_RESET OR RX_SRC_RDY_N);
   sig_data_fifo_wr_data(REAL_IN_WIDTH-1 downto 4)    <= RX_REM;
   sig_data_fifo_wr_data(3)                           <= RX_SOP_N;
   sig_data_fifo_wr_data(2)                           <= RX_EOP_N;
   sig_data_fifo_wr_data(1)                           <= RX_SOF_N;
   sig_data_fifo_wr_data(0)                           <= RX_EOF_N;

   -- --------------- DATA FIFO INSTANCE ------------------------------------
   data_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH      => REAL_IN_WIDTH
   )
   port map(
      RESET           => TX_RESET,
      
      -- Write interface
      WR_CLK          => RX_CLK,
      WR_DATA         => sig_data_fifo_wr_data,
      WR_WRITE        => sig_data_fifo_wr_write,
      WR_FULL         => open,
      WR_ALMOST_FULL  => open,
      
      -- Read interface
      RD_CLK          => TX_CLK,
      RD_DATA         => sig_data_fifo_rd_data,
      RD_READ         => sig_data_fifo_rd_read,
      RD_EMPTY        => sig_data_fifo_rd_empty,
      RD_ALMOST_EMPTY => sig_data_fifo_rd_almost_empty
   );

   sig_data_fifo_rd_read     <= '1';

   sig_rem             <= sig_data_fifo_rd_data(REAL_IN_WIDTH-1 downto 4);
   sig_sop_n           <= sig_data_fifo_rd_data(3);
   sig_eop_n           <= sig_data_fifo_rd_data(2);
   sig_sop_n           <= sig_data_fifo_rd_data(1);
   sig_sop_n           <= sig_data_fifo_rd_data(0);


   --
   sig_coverage_regs_en    <= NOT sig_data_fifo_rd_empty;
                                                     
   sig_reg_controls_in(0)  <=     (NOT sig_sof_n)    -- |SOF_N|EOF_N|SOP_N|EOP_N|
                              AND (NOT sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  0  |  0  |  0  |  0  |
   sig_reg_controls_in(1)  <=     (NOT sig_sof_n)
                              AND (    sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  0  |  1  |  0  |  0  |
   sig_reg_controls_in(2)  <=     (NOT sig_sof_n)
                              AND (    sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (    sig_eop_n);   -- |  0  |  1  |  0  |  1  |
   sig_reg_controls_in(3)  <=     (    sig_sof_n)
                              AND (NOT sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  1  |  0  |  0  |  0  |
   sig_reg_controls_in(4)  <=     (    sig_sof_n)
                              AND (NOT sig_eof_n)
                              AND (    sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  1  |  0  |  1  |  0  |
   sig_reg_controls_in(5)  <=     (    sig_sof_n)
                              AND (    sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  1  |  1  |  0  |  0  |
   sig_reg_controls_in(6)  <=     (    sig_sof_n)
                              AND (    sig_eof_n)
                              AND (NOT sig_sop_n)
                              AND (    sig_eop_n);   -- |  1  |  1  |  0  |  1  |
   sig_reg_controls_in(7)  <=     (    sig_sof_n)
                              AND (    sig_eof_n)
                              AND (    sig_sop_n)
                              AND (NOT sig_eop_n);   -- |  1  |  1  |  1  |  0  |
   sig_reg_controls_in(8)  <=     (    sig_sof_n)
                              AND (    sig_eof_n)
                              AND (    sig_sop_n)
                              AND (    sig_eop_n);   -- |  1  |  1  |  1  |  1  |

   -- the decoder of the DREM signal from binary to one hot
   decod_rem_p: process(sig_rem)
   begin
      sig_reg_drem_in <= (others => '0');

      for i in 0 to IN_DREM_NUM-1 loop
         if (i = unsigned(sig_rem)) then
            sig_reg_drem_in(i) <= '1';
         end if;
      end loop;
   end process;


   -- registers for holding the covered states
   coverage_regs_p: process(TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (TX_RESET = '1') then
            reg_controls <= (others => '0');
            reg_drem     <= (others => '0');
         elsif (sig_coverage_regs_en = '1') then
            reg_controls <= reg_controls OR sig_reg_controls_in;
            reg_drem     <= reg_drem     OR sig_reg_drem_in;
         end if;
      end if;
   end process;


   --
   reg_sample_in(CONTROL_NUM_STATES-1 downto 0)   <= reg_controls;
   reg_sample_in(IN_DREM_NUM-1+CONTROL_NUM_STATES downto CONTROL_NUM_STATES)
      <= reg_drem;

   reg_sample_en <= sig_sample;

   -- ------------------ SAMPLE REGISTER ------------------------------------
   reg_sample_p: process(TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (reg_sample_en = '1') then
            reg_sample <= reg_sample_in;
         end if;
      end if;
   end process;

   --
   reg_sample_valid_reg_set <= sig_sample;
   reg_sample_valid_reg_clr <= rx_rearranger_read_next;

   -- ------------ SAMPLE REGISTER VALIDITY REGISTER ------------------------
   reg_sample_valid_reg_p: process(TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (TX_RESET = '1') then
            reg_sample_valid_reg <= '0';
         elsif (reg_sample_valid_reg_set = '1') then
            reg_sample_valid_reg <= '1';
         elsif (reg_sample_valid_reg_clr = '1') then
            reg_sample_valid_reg <= '0';
         end if;
      end if;
   end process;

   --
   rx_rearranger_data(CONTROL_NUM_STATES-1 downto 0)
      <= reg_sample(CONTROL_NUM_STATES-1 downto 0);
   rx_rearranger_data(16 downto CONTROL_NUM_STATES) <= (others => '0');
   rx_rearranger_data(IN_DREM_NUM-1+16 downto 16) <=
      reg_sample(IN_DREM_NUM-1+CONTROL_NUM_STATES downto CONTROL_NUM_STATES);

   rx_rearranger_valid  <= reg_sample_valid_reg;

   -- --------------- REARRANGER instance ---------------------------
--   rearranger_i : entity work.REARRANGER
--   generic map(
--      IN_DATA_WIDTH   => TOTAL_STATE_SPACE_SIZE,
--      OUT_DATA_WIDTH  => OUT_DATA_WIDTH
--   )
--   port map(
--      CLK             => TX_CLK,
--      RESET           => TX_RESET,
--
--      -- RX interface
--      RX_DATA         => rx_rearranger_data,
--      RX_READ_NEXT    => rx_rearranger_read_next,
--      RX_VALID        => rx_rearranger_valid,
--
--      -- TX interface
--      TX_DATA         => tx_rearranger_data,
--      TX_READ_NEXT    => tx_rearranger_read_next,
--      TX_VALID        => tx_rearranger_valid
--   );

   -- substitution for the rearranger
   tx_rearranger_data      <= rx_rearranger_data;
   tx_rearranger_valid     <= rx_rearranger_valid;
   rx_rearranger_read_next <= tx_rearranger_read_next;

   --
   reg_rearranger_completed_set <= rx_rearranger_read_next;
   reg_rearranger_completed_clr <= sig_sample;

   -- ---------------- REARRANGER COMPLETED REGISTER ------------------------
   reg_rearranger_completed_p: process(TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (TX_RESET = '1') then
            reg_rearranger_completed <= '0';
         elsif (reg_rearranger_completed_set = '1') then
            reg_rearranger_completed <= '1';
         elsif (reg_rearranger_completed_clr = '1') then
            reg_rearranger_completed <= '0';
         end if;
      end if;
   end process;


   --
   acc_time_counter_clr <= sig_sample;
   acc_time_counter_en <= (NOT cmp_acc_time_counter_is_max) AND sig_coverage_regs_en;

   -- ---------------- ACCUMULATION TIME COUNTER ----------------------------
   acc_time_counter_p: process(TX_CLK)
   begin
      if (rising_edge(TX_CLK)) then
         if (TX_RESET = '1') then
            acc_time_counter <= (others => '0');
         elsif (acc_time_counter_clr = '1') then
            acc_time_counter <= (others => '0');
         elsif (acc_time_counter_en = '1') then
            acc_time_counter <= acc_time_counter + 1;
         end if;
      end if;
   end process;

   --
   cmp_acc_time_counter_is_max_in <= acc_time_counter;

   -- ----------- COMPARER OF THE ACCUMULATION TIME COUNTER -----------------
   cmp_acc_time_counter_is_max_p: process(cmp_acc_time_counter_is_max_in)
   begin
      cmp_acc_time_counter_is_max <= '0';

      if (cmp_acc_time_counter_is_max_in = SEND_INTERVAL) then
         cmp_acc_time_counter_is_max <= '1';
      end if;
   end process;

   sig_sample <= reg_rearranger_completed AND cmp_acc_time_counter_is_max;

   --
   rx_packetizer_data       <= tx_rearranger_data;
   tx_rearranger_read_next  <= rx_packetizer_read_next;
   rx_packetizer_valid      <= tx_rearranger_valid;

   -- --------------- PACKETIZER instance -------------------------------
   packetizer_i : entity work.PACKETIZER
   generic map(
      DATA_WIDTH      => OUT_DATA_WIDTH,
      ENDPOINT_ID     => ENDPOINT_ID,
      FRAME_LENGTH    => FRAME_LENGTH
   )
   port map(
      CLK             => TX_CLK,
      RESET           => TX_RESET,
      
      -- RX interface
      RX_DATA         => rx_packetizer_data,
      RX_READ_NEXT    => rx_packetizer_read_next,
      RX_VALID        => rx_packetizer_valid,

      -- TX interface
      TX_DATA         => tx_packetizer_data,
      TX_REM          => tx_packetizer_rem,
      TX_SOF_N        => tx_packetizer_sof_n,
      TX_EOF_N        => tx_packetizer_eof_n,
      TX_SOP_N        => tx_packetizer_sop_n,
      TX_EOP_N        => tx_packetizer_eop_n,
      TX_SRC_RDY_N    => tx_packetizer_src_rdy_n,
      TX_DST_RDY_N    => tx_packetizer_dst_rdy_n,

      PACKET_SENT     => open
   );

   -- --------------- MAPPING OF OUTPUT PORTS -------------------------------
   OUTPUT_READY <= sig_data_fifo_rd_almost_empty;

   TX_DATA                  <= tx_packetizer_data;
   TX_REM                   <= tx_packetizer_rem;
   TX_SOF_N                 <= tx_packetizer_sof_n;
   TX_EOF_N                 <= tx_packetizer_eof_n;
   TX_SOP_N                 <= tx_packetizer_sop_n;
   TX_EOP_N                 <= tx_packetizer_eop_n;
   TX_SRC_RDY_N             <= tx_packetizer_src_rdy_n;
   tx_packetizer_dst_rdy_n  <= TX_DST_RDY_N;

end architecture;
