-- verification_engine_tb.vhd: Verification engine testbench
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library work;
use work.math_pack.all;
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

entity testbench is
end entity;

architecture test of testbench is

   -- ------------------------------------------------------------------------
   --                                Constants
   -- ------------------------------------------------------------------------

   -- data width of the verification core
   constant DATA_WIDTH  : integer := 64;

   -- duration of reset
   constant RESET_TIME  : time := 100 ns;
   -- clock period
   constant CLK_PERIOD  : time := 10 ns;

   constant VER_CORE_ADDR     : std_logic_vector(31 downto 0) := X"00000000";

   constant GEN_RUN_ADDR      : std_logic_vector(31 downto 0) := X"00100000";
   constant GEN_SEED_ADDR     : std_logic_vector(31 downto 0) := X"00100004";

   constant RUN_REG_ADDR      : std_logic_vector(31 downto 0) := X"00101000";
   constant TRANS_REG_ADDR    : std_logic_vector(31 downto 0) := X"00101004";
   constant PART_NUM_REG_ADDR : std_logic_vector(31 downto 0) := X"00101010";
   constant PART_SIZE_REG_ADDR: std_logic_vector(31 downto 0) := X"00101080";
   constant PART_REG_OFFSET   : integer := 16;
   constant PART_MASK_OFFSET  : integer := 0;
   constant PART_BASE_OFFSET  : integer := 4;
   constant PART_MAX_OFFSET   : integer := 8;

   constant FL_COMMAND_ADDR   : std_logic_vector(31 downto 0) := X"00200000";

   constant TRANSACTION_COUNT : integer := 16#A0#;

   -- ------------------------------------------------------------------------
   --                                 Signals
   -- ------------------------------------------------------------------------

   -- common signals
   signal clk           : std_logic;
   signal reset         : std_logic;

   -- input FrameLink
   signal rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal rx_sof_n      : std_logic;
   signal rx_eof_n      : std_logic;
   signal rx_sop_n      : std_logic;
   signal rx_eop_n      : std_logic;
   signal rx_src_rdy_n  : std_logic;
   signal rx_dst_rdy_n  : std_logic;

   -- output FrameLink
   signal tx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal tx_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal tx_sof_n      : std_logic;
   signal tx_eof_n      : std_logic;
   signal tx_sop_n      : std_logic;
   signal tx_eop_n      : std_logic;
   signal tx_src_rdy_n  : std_logic;
   signal tx_dst_rdy_n  : std_logic;

   -- MI32 interface
   signal mi32_dwr      : std_logic_vector(31 downto 0);
   signal mi32_addr     : std_logic_vector(31 downto 0);
   signal mi32_rd       : std_logic;
   signal mi32_wr       : std_logic;
   signal mi32_be       : std_logic_vector(3 downto 0);
   signal mi32_drd      : std_logic_vector(31 downto 0);
   signal mi32_ardy     : std_logic;
   signal mi32_drdy     : std_logic;

begin

   -- -----------------------------------------------------------------------
   --                             Unit under test
   -- -----------------------------------------------------------------------
   uut: entity work.verification_engine
   generic map(
      DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      CLK            => clk,
      RESET          => reset,

      -- input interface
      RX_DATA        => rx_data,
      RX_REM         => rx_rem,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,

      -- output interface
      TX_DATA        => tx_data,
      TX_REM         => tx_rem,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n,

      -- MI32 interface
      MI32_DWR       => mi32_dwr,
      MI32_ADDR      => mi32_addr,
      MI32_RD        => mi32_rd,
      MI32_WR        => mi32_wr,
      MI32_BE        => mi32_be,
      MI32_DRD       => mi32_drd,
      MI32_ARDY      => mi32_ardy,
      MI32_DRDY      => mi32_drdy
   );


   -- -------------------------------------------------------------------------
   --                           Input FL_BFM
   -- -------------------------------------------------------------------------
   FL_BFM_I: entity work.FL_BFM
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      FL_BFM_ID => 00
   )
   port map (
      -- Common interface
      RESET           => reset,
      CLK             => clk,

      TX_DATA         => rx_data,
      TX_REM          => rx_rem,
      TX_SOF_N        => rx_sof_n,
      TX_EOF_N        => rx_eof_n,
      TX_SOP_N        => rx_sop_n,
      TX_EOP_N        => rx_eop_n,
      TX_SRC_RDY_N    => rx_src_rdy_n,
      TX_DST_RDY_N    => rx_dst_rdy_n
   ); 

   -- -------------------------------------------------------------------------
   --                           Output FL_MONITOR
   -- -------------------------------------------------------------------------
   FL_MONITOR_I : entity work.MONITOR
   generic map (
      RX_TX_DATA_WIDTH => DATA_WIDTH,
      FILE_NAME  => "./monitor.txt",
      FRAME_PARTS => 1,
      RDY_DRIVER => RND
   )
   port map (
      -- Common interface
      FL_RESET        => reset,
      FL_CLK          => clk,

      RX_DATA         => tx_data,
      RX_REM          => tx_rem,
      RX_SOF_N        => tx_sof_n,
      RX_EOF_N        => tx_eof_n,
      RX_SOP_N        => tx_sop_n,
      RX_EOP_N        => tx_eop_n,
      RX_SRC_RDY_N    => tx_src_rdy_n,
      RX_DST_RDY_N    => tx_dst_rdy_n
   ); 

   -- -------------------------------------------------------------------------
   --                           CLOCKs & RESETs
   -- -------------------------------------------------------------------------
   resetp : process
   begin
      reset <= '1', '0' after RESET_TIME;
      wait;
   end process;

   clk_genp: process
   begin
      clk  <= '1';
      wait for CLK_PERIOD/2;
      clk  <= '0';
      wait for CLK_PERIOD/2;
   end process;



   -- -----------------------------------------------------------------------
   --                                 Test
   -- -----------------------------------------------------------------------
   tb : process
   begin

      -- initialisation of signals
      mi32_rd    <= '0';
      mi32_wr    <= '0';
      mi32_be    <= "1111";
      mi32_dwr   <= (others => '0');
      mi32_addr  <= X"DEADBEEF";

      wait for RESET_TIME;
      wait until rising_edge(clk);

      -- initialization of registers


      mi32_wr    <= '1';

      -- ----------- PARTS NUM --------------
      -- PARTS_NUM_MASK
      mi32_addr  <= PART_NUM_REG_ADDR + PART_MASK_OFFSET;
      mi32_dwr   <= X"00000000";
      wait until rising_edge(clk);

      -- PARTS_NUM_BASE
      mi32_addr  <= PART_NUM_REG_ADDR + PART_BASE_OFFSET;
      mi32_dwr   <= X"00000000";
      wait until rising_edge(clk);

      -- PARTS_NUM_MAX
      mi32_addr  <= PART_NUM_REG_ADDR + PART_MAX_OFFSET;
      mi32_dwr   <= X"00000000";
      wait until rising_edge(clk);

      -- ----------- PART 0 -----------------
      -- PART0_MASK
      mi32_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_MASK_OFFSET;
      mi32_dwr   <= X"00000000";
      wait until rising_edge(clk);

      -- PART0_BASE
      mi32_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_BASE_OFFSET;
      mi32_dwr   <= X"00000040";
      wait until rising_edge(clk);

      -- PART0_MAX
      mi32_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_MAX_OFFSET;
      mi32_dwr   <= X"00000000";
      wait until rising_edge(clk);

--      -- ----------- PART 1 -----------------
--      -- PART1_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"000000FF";
--      wait until rising_edge(clk);
--
--      -- PART1_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"00000010";
--      wait until rising_edge(clk);
--
--      -- PART1_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"000000A0";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 2 -----------------
--      -- PART2_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"00000FFF";
--      wait until rising_edge(clk);
--
--      -- PART2_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"00000100";
--      wait until rising_edge(clk);
--
--      -- PART2_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"00000A00";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 3 -----------------
--      -- PART3_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"0000FFFF";
--      wait until rising_edge(clk);
--
--      -- PART3_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"00001000";
--      wait until rising_edge(clk);
--
--      -- PART3_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"0000A000";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 4 -----------------
--      -- PART4_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"000FFFFF";
--      wait until rising_edge(clk);
--
--      -- PART4_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"00010000";
--      wait until rising_edge(clk);
--
--      -- PART4_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"000A0000";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 5 -----------------
--      -- PART5_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"00FFFFFF";
--      wait until rising_edge(clk);
--
--      -- PART5_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"00100000";
--      wait until rising_edge(clk);
--
--      -- PART5_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"00A00000";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 6 -----------------
--      -- PART6_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"0FFFFFFF";
--      wait until rising_edge(clk);
--
--      -- PART6_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"01000000";
--      wait until rising_edge(clk);
--
--      -- PART6_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"0A000000";
--      wait until rising_edge(clk);
--
--      -- ----------- PART 7 -----------------
--      -- PART7_MASK
--      mi32_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_MASK_OFFSET;
--      mi32_dwr   <= X"FFFFFFFF";
--      wait until rising_edge(clk);
--
--      -- PART7_BASE
--      mi32_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_BASE_OFFSET;
--      mi32_dwr   <= X"10000000";
--      wait until rising_edge(clk);
--
--      -- PART7_MAX
--      mi32_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_MAX_OFFSET;
--      mi32_dwr   <= X"A0000000";
--      wait until rising_edge(clk);

      -- ------- TRANSACTION COUNT -----------
      mi32_addr  <= TRANS_REG_ADDR;
      mi32_dwr   <= conv_std_logic_vector(TRANSACTION_COUNT, 32);
      wait until rising_edge(clk);

      -- -------------- GENERATOR SEED --------
      mi32_addr  <= GEN_SEED_ADDR;
      mi32_dwr   <= X"00011ACA";
      wait until rising_edge(clk);

      -- -------------- RUN GENERATOR --------
      mi32_addr  <= GEN_RUN_ADDR;
      mi32_dwr   <= X"00000001";
      wait until rising_edge(clk);

      -- -------------- RUN ADAPTER ----------
      mi32_addr  <= RUN_REG_ADDR;
      mi32_dwr   <= X"00000001";
      wait until rising_edge(clk);
      mi32_wr    <= '0';

      wait for 15000*CLK_PERIOD;

      -- -------------- WAIT FOREVER ----------
      mi32_addr  <= FL_COMMAND_ADDR;
      mi32_dwr   <= X"00000001";
      mi32_wr    <= '1';
      wait for CLK_PERIOD;
      mi32_wr    <= '0';

      wait for 3000*CLK_PERIOD;

      mi32_addr  <= X"00F00014";
      mi32_rd    <= '1';
      wait for CLK_PERIOD;
      mi32_rd    <= '0';

      wait for 10*CLK_PERIOD;

      mi32_addr  <= X"00F00018";
      mi32_rd    <= '1';
      wait for CLK_PERIOD;

      mi32_rd    <= '0';

      wait;
   end process;


end architecture;
