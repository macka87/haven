-- netcope_adder_tb.vhd: Testbench for FrameLink Adder of NetCOPE header
-- Copyright (C) 2011 
-- Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
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
   constant DATA_WIDTH    : integer := 64;  
   constant DELAY_WIDTH   : integer := 9;

   constant clkper        : time := 10 ns; 
   constant reset_time    : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal fl_driver_rx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_driver_rx_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_driver_rx_sof_n        : std_logic;
   signal fl_driver_rx_sop_n        : std_logic;
   signal fl_driver_rx_eof_n        : std_logic;
   signal fl_driver_rx_eop_n        : std_logic;
   signal fl_driver_rx_src_rdy_n    : std_logic;
   signal fl_driver_rx_dst_rdy_n    : std_logic;
   
   -- UUT output signals
   signal fl_driver_tx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_driver_tx_src_rdy_n    : std_logic;
   signal fl_driver_tx_dst_rdy_n    : std_logic;
   
   signal fl_driver_tx_delay        : std_logic_vector(DELAY_WIDTH-1 downto 0);
   signal fl_driver_tx_delay_wr_n   : std_logic;
   signal fl_driver_tx_delay_rdy_n  : std_logic;
   
   signal fl_driver_tx_finish       : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.FL_DRIVER_CTRL
      generic map (
         DATA_WIDTH        => DATA_WIDTH,
         DELAY_WIDTH       => DELAY_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,

         RX_DATA           => fl_driver_rx_data,
         RX_REM            => fl_driver_rx_rem,
         RX_SOF_N          => fl_driver_rx_sof_n,
         RX_SOP_N          => fl_driver_rx_sop_n,
         RX_EOP_N          => fl_driver_rx_eop_n,
         RX_EOF_N          => fl_driver_rx_eof_n,
         RX_SRC_RDY_N      => fl_driver_rx_src_rdy_n,
         RX_DST_RDY_N      => fl_driver_rx_dst_rdy_n,
         
         TX_DATA           => fl_driver_tx_data,
         TX_SRC_RDY_N      => fl_driver_tx_src_rdy_n,
         TX_DST_RDY_N      => fl_driver_tx_dst_rdy_n,
         
         TX_DELAY          => fl_driver_tx_delay,
         TX_DELAY_WR_N     => fl_driver_tx_delay_wr_n,
         TX_DELAY_RDY_N    => fl_driver_tx_delay_rdy_n, 
         
         TX_FINISH         => fl_driver_tx_finish
      );

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
      wait for 30*clkper;
      wait until rising_edge(clk);
      -- data header - first part  
      fl_driver_rx_data  <= X"0201000000000000"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '0';
      fl_driver_rx_eof_n <= '1';
      fl_driver_rx_sop_n <= '0';
      fl_driver_rx_eop_n <= '1';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      -- data - first part 
      fl_driver_rx_data  <= X"1234567812345678"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '1';
      fl_driver_rx_eof_n <= '0';
      fl_driver_rx_sop_n <= '1';
      fl_driver_rx_eop_n <= '0';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
   
      wait until rising_edge(clk);
      -- data header - second part  
      fl_driver_rx_data  <= X"0301000000000000"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '0';
      fl_driver_rx_eof_n <= '1';
      fl_driver_rx_sop_n <= '0';
      fl_driver_rx_eop_n <= '1';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      -- data - second part
      fl_driver_rx_data  <= X"0000000000004321"; 
      fl_driver_rx_rem   <= "011";
      fl_driver_rx_sof_n <= '1';
      fl_driver_rx_eof_n <= '0';
      fl_driver_rx_sop_n <= '1';
      fl_driver_rx_eop_n <= '0';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
       
      wait until rising_edge(clk);
      -- delay header   
      fl_driver_rx_data  <= X"0001000500000000"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '0';
      fl_driver_rx_eof_n <= '1';
      fl_driver_rx_sop_n <= '0';
      fl_driver_rx_eop_n <= '1';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      
      -- delay 
      fl_driver_rx_data  <= X"0000000000000201"; 
      fl_driver_rx_rem   <= "001";
      fl_driver_rx_sof_n <= '1';
      fl_driver_rx_eof_n <= '0';
      fl_driver_rx_sop_n <= '1';
      fl_driver_rx_eop_n <= '0';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      fl_driver_rx_src_rdy_n <= '1';
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      
      -- wait header   
      fl_driver_rx_data  <= X"0001000200000000"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '0';
      fl_driver_rx_eof_n <= '1';
      fl_driver_rx_sop_n <= '0';
      fl_driver_rx_eop_n <= '1';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      -- wait 
      fl_driver_rx_data  <= X"0000000000000100"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '1';
      fl_driver_rx_eof_n <= '0';
      fl_driver_rx_sop_n <= '1';
      fl_driver_rx_eop_n <= '0';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      fl_driver_rx_src_rdy_n <= '1';
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      -- stop header   
      fl_driver_rx_data  <= X"0001000400000000"; 
      fl_driver_rx_rem   <= "111";
      fl_driver_rx_sof_n <= '0';
      fl_driver_rx_eof_n <= '0';
      fl_driver_rx_sop_n <= '0';
      fl_driver_rx_eop_n <= '0';
      fl_driver_rx_src_rdy_n <= '0';
      fl_driver_tx_dst_rdy_n <= '0';
      fl_driver_tx_delay_rdy_n <= '0';
      
      wait until rising_edge(clk);
      fl_driver_rx_src_rdy_n <= '1';

      -- wait forever
      wait;
   end process;
end architecture behavioral;
