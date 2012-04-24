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
   constant DATA_WIDTH        : integer := 64;
   constant DELAY_WIDTH       : integer := 9;

   constant wr_clkper         : time := 10 ns; 
   constant rd_clkper         : time := 15 ns;
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal wr_clk              : std_logic;
   signal rd_clk              : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal fl_async_unit_rx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_async_unit_rx_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_async_unit_rx_sof_n        : std_logic;
   signal fl_async_unit_rx_sop_n        : std_logic;
   signal fl_async_unit_rx_eof_n        : std_logic;
   signal fl_async_unit_rx_eop_n        : std_logic;
   signal fl_async_unit_rx_src_rdy_n    : std_logic;
   signal fl_async_unit_rx_dst_rdy_n    : std_logic;
   
   signal fl_async_unit_rx_delay        : std_logic_vector(DELAY_WIDTH-1 downto 0);
   signal fl_async_unit_rx_delay_wr_n   : std_logic;
   signal fl_async_unit_rx_delay_rdy_n  : std_logic;
   
   signal fl_async_unit_rx_finish       : std_logic;

   -- UUT output signals
   signal fl_async_unit_tx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_async_unit_tx_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_async_unit_tx_sof_n        : std_logic;
   signal fl_async_unit_tx_sop_n        : std_logic;
   signal fl_async_unit_tx_eof_n        : std_logic;
   signal fl_async_unit_tx_eop_n        : std_logic;
   signal fl_async_unit_tx_src_rdy_n    : std_logic;
   signal fl_async_unit_tx_dst_rdy_n    : std_logic;
   
   signal fl_async_unit_tx_output_rdy   : std_logic;
   signal rd_clk_en                     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL Shortener
   -- -------------------------------------------------------------------------
   uut: entity work.TX_ASYNC_FL_UNIT
      generic map (
         DATA_WIDTH        => DATA_WIDTH,
         DELAY_WIDTH       => DELAY_WIDTH
      )
      port map (
         WR_CLK            => WR_CLK,
         RD_CLK            => RD_CLK, 
         RESET             => RESET,

         RX_DATA           => fl_async_unit_rx_data,
         RX_REM            => fl_async_unit_rx_rem,
         RX_SOF_N          => fl_async_unit_rx_sof_n,
         RX_SOP_N          => fl_async_unit_rx_sop_n,
         RX_EOP_N          => fl_async_unit_rx_eop_n,
         RX_EOF_N          => fl_async_unit_rx_eof_n,
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
      if ((rd_clk_en = '1') or (reset = '1')) then      
        rd_clk <= '1';
      else
        rd_clk <= '0';
      end if;
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
      rd_clk_en <= '0';
   
      fl_async_unit_rx_data <= X"0000000000000000";
      fl_async_unit_rx_rem  <= "000";
      fl_async_unit_rx_sof_n  <= '1';
      fl_async_unit_rx_eof_n  <= '1';
      fl_async_unit_rx_sop_n  <= '1';
      fl_async_unit_rx_eop_n  <= '1';
      fl_async_unit_rx_src_rdy_n <= '1';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"00";
      fl_async_unit_rx_delay_wr_n <= '1';
      fl_async_unit_tx_dst_rdy_n <= '1';
   
      wait for reset_time; 
      wait until (fl_async_unit_rx_dst_rdy_n = '0');
      wait until rising_edge(wr_clk);
      
      fl_async_unit_rx_data <= X"1234567812345678"; --& "111" & '0' & '0' & '1' & '0';
      fl_async_unit_rx_rem  <= "111";
      fl_async_unit_rx_sof_n  <= '0';
      fl_async_unit_rx_eof_n  <= '1';
      fl_async_unit_rx_sop_n  <= '0';
      fl_async_unit_rx_eop_n  <= '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"01";
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);
       
      fl_async_unit_rx_data <= X"8765432187654321"; --& "111" & '1' & '0' & '1' & '1';
      fl_async_unit_rx_rem  <= "111";
      fl_async_unit_rx_sof_n  <= '1';
      fl_async_unit_rx_eof_n  <= '1';
      fl_async_unit_rx_sop_n  <= '0';
      fl_async_unit_rx_eop_n  <= '1';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"02";
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);

      rd_clk_en <= '1';

      fl_async_unit_rx_data <= X"0000000000004321"; --& "011" & '0' & '1' & '0' & '1';
      fl_async_unit_rx_rem  <= "011";
      fl_async_unit_rx_sof_n  <= '1';
      fl_async_unit_rx_eof_n  <= '0';
      fl_async_unit_rx_sop_n  <= '1';
      fl_async_unit_rx_eop_n  <= '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"00";
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);
      
      fl_async_unit_rx_delay <= "1" & X"0A";
      fl_async_unit_rx_src_rdy_n <= '1';
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);
       
      fl_async_unit_rx_data <= X"1122334411223344"; --& "111" & '0' & '0' & '1' & '0';
      fl_async_unit_rx_rem  <= "111";
      fl_async_unit_rx_sof_n  <= '0';
      fl_async_unit_rx_eof_n  <= '1';
      fl_async_unit_rx_sop_n  <= '0';
      fl_async_unit_rx_eop_n  <= '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"05";
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);
       
      fl_async_unit_rx_data <= X"4433221144332211"; --& "111" & '0' & '0' & '0' & '1';
      fl_async_unit_rx_rem  <= "111";
      fl_async_unit_rx_sof_n  <= '1';
      fl_async_unit_rx_eof_n  <= '0';
      fl_async_unit_rx_sop_n  <= '0';
      fl_async_unit_rx_eop_n  <= '0';
      fl_async_unit_rx_src_rdy_n <= '0';
      fl_async_unit_rx_finish <= '0';
      fl_async_unit_rx_delay <= "0" & X"00";
      fl_async_unit_rx_delay_wr_n <= '0';
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait until rising_edge(wr_clk);
      fl_async_unit_rx_delay_wr_n <= '1';
      fl_async_unit_rx_src_rdy_n <= '1';

      wait for 8*wr_clkper;
      fl_async_unit_rx_finish <= '1';

      
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      fl_async_unit_tx_dst_rdy_n <= '1';
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      wait until rising_edge(rd_clk);
      fl_async_unit_tx_dst_rdy_n <= '0';
      
      wait;
   end process;
end architecture behavioral;
