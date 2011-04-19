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
   constant IN_DATA_WIDTH     : integer := 71;  
   constant OUT_DATA_WIDTH    : integer := 46;
   constant DELAY_WIDTH       : integer := 8;

   constant wr_clkper         : time := 10 ns; 
   constant rd_clkper         : time := 15 ns;
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal wr_clk              : std_logic;
   signal rd_clk              : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal fl_async_unit_rx_data         : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal fl_async_unit_rx_src_rdy_n    : std_logic;
   signal fl_async_unit_rx_dst_rdy_n    : std_logic;
   
   signal fl_async_unit_rx_delay        : std_logic_vector(DELAY_WIDTH-1 downto 0);
   signal fl_async_unit_rx_delay_wr_n   : std_logic;
   signal fl_async_unit_rx_delay_rdy_n  : std_logic;
   
   signal fl_async_unit_rx_finish       : std_logic;

   -- UUT output signals
   signal fl_async_unit_tx_data         : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal fl_async_unit_tx_rem          : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
   signal fl_async_unit_tx_sof_n        : std_logic;
   signal fl_async_unit_tx_sop_n        : std_logic;
   signal fl_async_unit_tx_eof_n        : std_logic;
   signal fl_async_unit_tx_eop_n        : std_logic;
   signal fl_async_unit_tx_src_rdy_n    : std_logic;
   signal fl_async_unit_tx_dst_rdy_n    : std_logic;
   
   signal fl_async_unit_tx_output_rdy   : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.TX_ASYNC_FL_UNIT
      generic map (
         IN_DATA_WIDTH     => IN_DATA_WIDTH,
         OUT_DATA_WIDTH    => OUT_DATA_WIDTH,
         DELAY_WIDTH       => DELAY_WIDTH
      )
      port map (
         WR_CLK            => WR_CLK,
         RD_CLK            => RD_CLK, 
         RESET             => RESET,

         RX_DATA           => fl_async_unit_rx_data,
         RX_SRC_RDY_N      => fl_async_unit_rx_src_rdy_n,
         RX_DST_RDY_N      => fl_async_unit_rx_dst_rdy_n,
         
         RX_DELAY          => fl_async_unit_rx_delay,
         RX_DELAY_WR_N     => fl_async_unit_rx_delay_wr_n,
         RX_DELAY_RDY_N    => fl_async_unit_rx_delay_rdy_n, 
         
         RX_FINISH         => fl_async_unit_rx_finish,

         TX_DATA           => fl_async_unit_tx_data,
         TX_REM            => fl_async_unit_tx_rem,
         TX_SOF_N          => fl_async_unit_tx_sof_n,
         TX_SOP_N          => fl_async_unit_tx_sop_n,
         TX_EOP_N          => fl_async_unit_tx_eop_n,
         TX_EOF_N          => fl_async_unit_tx_eof_n,
         TX_SRC_RDY_N      => fl_async_unit_tx_src_rdy_n,
         TX_DST_RDY_N      => fl_async_unit_tx_dst_rdy_n,
         
         OUTPUT_RDY        => fl_async_unit_tx_output_rdy
      );

   -- ----------------------------------------------------

   -- CLK generator
   wrclkgen: process
   begin
      wr_clk <= '1';
      wait for wr_clkper/2;
      wr_clk <= '0';
      wait for wr_clkper/2;
   end process;
   
   rdclkgen: process
   begin
      rd_clk <= '1';
      wait for rd_clkper/2;
      rd_clk <= '0';
      wait for rd_clkper/2;
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
      fl_async_unit_rx_data <= X"1234567812345678" & "111" & '0' & '0' & '1' & '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= X"00";
      fl_async_unit_rx_delay_wr_n <= '0';
      
      wait for 1*wr_clkper;
       
      fl_async_unit_rx_data <= X"8765432187654321" & "111" & '1' & '0' & '1' & '1';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= X"02";
      fl_async_unit_rx_delay_wr_n <= '0';
      
      wait for 1*wr_clkper;
       
      fl_async_unit_rx_data <= X"0000000000004321" & "011" & '0' & '1' & '0' & '1';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= X"00";
      fl_async_unit_rx_delay_wr_n <= '0';
      
      wait for 1*wr_clkper;
       
      fl_async_unit_rx_data <= X"1122334411223344" & "111" & '0' & '0' & '1' & '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= X"05";
      fl_async_unit_rx_delay_wr_n <= '0';
      
      wait for 1*wr_clkper;
       
      fl_async_unit_rx_data <= X"4433221144332211" & "111" & '0' & '0' & '0' & '1';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= X"00";
      fl_async_unit_rx_delay_wr_n <= '0';
      
      wait;
   end process;
end architecture behavioral;
