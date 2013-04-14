-- verification_core_tb.vhd: Verification core testbench
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

library work;
use work.math_pack.all;
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

-- HAVEN constants
use work.haven_const.all;

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

begin

   -- -----------------------------------------------------------------------
   --                             Unit under test
   -- -----------------------------------------------------------------------
   uut: entity work.verification_core
   generic map(
      -- data width 
      DATA_WIDTH         => DATA_WIDTH,
      -- the CORE_TYPE generic specifies the verified unit in the core
      CORE_TYPE          => core_fifo,
      -- should signal observers be used?
      USE_OBSERVERS      => false,
      -- should the input FrameLink coverage unit be used?
      USE_FL_COV_UNIT    => true
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
   --                             MI32 interface
   -- -----------------------------------------------------------------------

   mi32_dwr      <= (others => '0');
   mi32_addr     <= (others => '0');
   mi32_rd       <= '0';
   mi32_wr       <= '0';
   mi32_be       <= (others => '0');


   -- -----------------------------------------------------------------------
   --                                 Test
   -- -----------------------------------------------------------------------
   tb : process
   begin

      wait for RESET_TIME;

--      SendWriteFile("./input.txt2", RND, flCmd_0, 0);

      SendWriteFile("./start.txt", RND, flCmd_0, 0);

--      SendWriteFile("./boggus.txt", RND, flCmd_0, 0);

--      SendWriteFile("./input.txt", RND, flCmd_0, 0);
      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);

      SendWriteFile("./stop.txt", RND, flCmd_0, 0);

      wait;
   end process;


end architecture;
