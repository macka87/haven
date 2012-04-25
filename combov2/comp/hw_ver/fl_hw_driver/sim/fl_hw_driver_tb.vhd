-- netcope_adder_tb.vhd: Testbench for FrameLink Adder of NetCOPE header
-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;
use work.math_pack.all;

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
   constant IN_DATA_WIDTH     : integer := 64;
   constant OUT_DATA_WIDTH    : integer := 64;

   constant rx_clkper         : time := 10 ns; 
   constant tx_clkper         : time := 15 ns;
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal rx_clk              : std_logic;
   signal rx_reset            : std_logic;
   signal tx_clk              : std_logic;
   signal tx_reset            : std_logic;
   
   -- UUT input signals
   signal fl_driver_rx_data         : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal fl_driver_rx_rem          : std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
   signal fl_driver_rx_sof_n        : std_logic;
   signal fl_driver_rx_sop_n        : std_logic;
   signal fl_driver_rx_eof_n        : std_logic;
   signal fl_driver_rx_eop_n        : std_logic;
   signal fl_driver_rx_src_rdy_n    : std_logic;
   signal fl_driver_rx_dst_rdy_n    : std_logic;
   
   -- UUT output signals
   signal fl_driver_tx_data         : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal fl_driver_tx_rem          : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
   signal fl_driver_tx_sof_n        : std_logic;
   signal fl_driver_tx_sop_n        : std_logic;
   signal fl_driver_tx_eof_n        : std_logic;
   signal fl_driver_tx_eop_n        : std_logic;
   signal fl_driver_tx_src_rdy_n    : std_logic;
   signal fl_driver_tx_dst_rdy_n    : std_logic;
   
   signal fl_driver_tx_output_rdy   : std_logic;
   signal tx_clk_en                     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL HW Driver
   -- -------------------------------------------------------------------------
   uut: entity work.FL_HW_DRIVER
      generic map (
         IN_DATA_WIDTH     => IN_DATA_WIDTH,
         OUT_DATA_WIDTH    => OUT_DATA_WIDTH
      )
      port map (
         RX_CLK            => rx_clk,
         RX_RESET          => rx_reset,
         TX_CLK            => tx_clk, 
         TX_RESET          => tx_reset,

         RX_DATA           => fl_driver_rx_data,
         RX_REM            => fl_driver_rx_rem,
         RX_SOF_N          => fl_driver_rx_sof_n,
         RX_SOP_N          => fl_driver_rx_sop_n,
         RX_EOP_N          => fl_driver_rx_eop_n,
         RX_EOF_N          => fl_driver_rx_eof_n,
         RX_SRC_RDY_N      => fl_driver_rx_src_rdy_n,
         RX_DST_RDY_N      => fl_driver_rx_dst_rdy_n,
         
         TX_DATA           => fl_driver_tx_data,
         TX_REM            => fl_driver_tx_rem,
         TX_SOF_N          => fl_driver_tx_sof_n,
         TX_SOP_N          => fl_driver_tx_sop_n,
         TX_EOP_N          => fl_driver_tx_eop_n,
         TX_EOF_N          => fl_driver_tx_eof_n,
         TX_SRC_RDY_N      => fl_driver_tx_src_rdy_n,
         TX_DST_RDY_N      => fl_driver_tx_dst_rdy_n,
         
         OUTPUT_READY      => fl_driver_tx_output_rdy
      );
      
   -- ----------------------------------------------------

   -- -------------------------------------------------------------------------
   --                           Input FL_BFM
   -- -------------------------------------------------------------------------
   FL_BFM_I: entity work.FL_BFM
   generic map (
      DATA_WIDTH => IN_DATA_WIDTH,
      FL_BFM_ID => 00
   )
   port map (
      -- Common interface
      RESET           => rx_reset,
      CLK             => rx_clk,

      TX_DATA         => fl_driver_rx_data,
      TX_REM          => fl_driver_rx_rem,
      TX_SOF_N        => fl_driver_rx_sof_n,
      TX_EOF_N        => fl_driver_rx_eof_n,
      TX_SOP_N        => fl_driver_rx_sop_n,
      TX_EOP_N        => fl_driver_rx_eop_n,
      TX_SRC_RDY_N    => fl_driver_rx_src_rdy_n,
      TX_DST_RDY_N    => fl_driver_rx_dst_rdy_n
   ); 


   -- CLK generator
   rxclkgen: process
   begin
      rx_clk <= '1';
      wait for rx_clkper/2;
      rx_clk <= '0';
      wait for rx_clkper/2;
   end process;
   
   txclkgen: process
   begin
      if ((tx_clk_en = '1') or (tx_reset = '1')) then      
        tx_clk <= '1';
      else
        tx_clk <= '0';
      end if;
      wait for tx_clkper/2;
      tx_clk <= '0';
      wait for tx_clkper/2;
   end process;

   resetgen: process
   begin
      rx_reset <= '1';
      tx_reset <= '1';
      wait for reset_time;
      rx_reset <= '0';
      tx_reset <= '0';
      wait;
   end process;

   tb: process

   begin
      tx_clk_en <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
   
      wait for reset_time; 
      wait until rising_edge(rx_clk);
      
--      SendWriteFile("./start.txt", RND, flCmd_0, 0);

--      SendWriteFile("./boggus.txt", RND, flCmd_0, 0);
      SendWriteFile("./input.txt", RND, flCmd_0, 0);
      
      tx_clk_en <= '1';

----      SendWriteFile("./input.txt", RND, flCmd_0, 0);
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
--      SendWriteFile("./small.txt", RND, flCmd_0, 0);

      --SendWriteFile("./stop.txt", RND, flCmd_0, 0);
      
      wait;
   end process;
end architecture behavioral;
