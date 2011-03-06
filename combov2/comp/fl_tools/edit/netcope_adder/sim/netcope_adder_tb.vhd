-- netcope_adder_tb.vhd: Testbench for FrameLink Adder of NetCOPE header
-- Copyright (C) 2011 
-- Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- constants declarations
   ----------------------------------------------------------------------------
   constant DATA_WIDTH        : integer := 128;

   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   constant fl_bfm_id  : integer := 0;     -- ID of fl_bfm component   

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal fl_netcope_adder_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_rx_sof_n     : std_logic;
   signal fl_netcope_adder_rx_sop_n     : std_logic;
   signal fl_netcope_adder_rx_eop_n     : std_logic;
   signal fl_netcope_adder_rx_eof_n     : std_logic;
   signal fl_netcope_adder_rx_src_rdy_n : std_logic;
   signal fl_netcope_adder_rx_dst_rdy_n : std_logic;

   -- UUT output signals
   signal fl_netcope_adder_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_tx_sof_n     : std_logic;
   signal fl_netcope_adder_tx_sop_n     : std_logic;
   signal fl_netcope_adder_tx_eof_n     : std_logic;
   signal fl_netcope_adder_tx_eop_n     : std_logic;
   signal fl_netcope_adder_tx_src_rdy_n : std_logic;
   signal fl_netcope_adder_tx_dst_rdy_n : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.FL_NETCOPE_ADDER
      generic map (
         DATA_WIDTH        => DATA_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,

         RX_DATA           => fl_netcope_adder_rx_data,
         RX_REM            => fl_netcope_adder_rx_rem,
         RX_SOF_N          => fl_netcope_adder_rx_sof_n,
         RX_SOP_N          => fl_netcope_adder_rx_sop_n,
         RX_EOP_N          => fl_netcope_adder_rx_eop_n,
         RX_EOF_N          => fl_netcope_adder_rx_eof_n,
         RX_SRC_RDY_N      => fl_netcope_adder_rx_src_rdy_n,
         RX_DST_RDY_N      => fl_netcope_adder_rx_dst_rdy_n,

         TX_DATA           => fl_netcope_adder_tx_data,
         TX_REM            => fl_netcope_adder_tx_rem,
         TX_SOF_N          => fl_netcope_adder_tx_sof_n,
         TX_SOP_N          => fl_netcope_adder_tx_sop_n,
         TX_EOP_N          => fl_netcope_adder_tx_eop_n,
         TX_EOF_N          => fl_netcope_adder_tx_eof_n,
         TX_SRC_RDY_N      => fl_netcope_adder_tx_src_rdy_n,
         TX_DST_RDY_N      => fl_netcope_adder_tx_dst_rdy_n
      );

   
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component
   -- -------------------------------------------------------------------------
   fl_bfm_0: entity work.fl_bfm
      generic map(
         DATA_WIDTH      => data_width,
         FL_BFM_ID       => fl_bfm_id
      )
      port map(
         CLK          => clk,
         RESET        => reset,
 
         TX_DATA      => fl_netcope_adder_rx_data,
         TX_REM       => fl_netcope_adder_rx_rem,
         TX_SRC_RDY_N => fl_netcope_adder_rx_src_rdy_n,
         TX_DST_RDY_N => fl_netcope_adder_rx_dst_rdy_n,
         TX_SOP_N     => fl_netcope_adder_rx_sop_n,
         TX_EOP_N     => fl_netcope_adder_rx_eop_n,
         TX_SOF_N     => fl_netcope_adder_rx_sof_n,
         TX_EOF_N     => fl_netcope_adder_rx_eof_n         
      )
   ;
   
   monitor: entity work.monitor
      generic map(
         RX_TX_DATA_WIDTH  => data_width,
         FILE_NAME         => "./fl_out.txt",
         FRAME_PARTS       => 2,
         RDY_DRIVER        => RND
      )
      port map(
         FL_RESET          => reset,
         FL_CLK            => clk,
         
         RX_DATA           => fl_netcope_adder_tx_data,
         RX_REM            => fl_netcope_adder_tx_rem,
         RX_SOF_N          => fl_netcope_adder_tx_sof_n,
         RX_EOF_N          => fl_netcope_adder_tx_eof_n,
         RX_SOP_N          => fl_netcope_adder_tx_sop_n,
         RX_EOP_N          => fl_netcope_adder_tx_eop_n,
         RX_SRC_RDY_N      => fl_netcope_adder_tx_src_rdy_n,
         RX_DST_RDY_N      => fl_netcope_adder_tx_dst_rdy_n
      )
   ;

      
   -- ----------------------------------------------------

   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process

   begin
      wait for 3*reset_time;
       SendWriteFile("./fl_sim_send.txt", RND, flCmd_0, 0);

      wait;
   end process;
end architecture behavioral;
