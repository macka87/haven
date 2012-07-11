-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;

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
   constant DATA_WIDTH          : integer := 64;
   constant DREM_WIDTH          : integer := log2(DATA_WIDTH/8);

   constant IFCS                : integer := 2;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal test_unit_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal test_unit_fl_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal test_unit_fl_src_rdy_n : std_logic;
   signal test_unit_fl_dst_rdy_n : std_logic;
   signal test_unit_fl_sop_n     : std_logic;
   signal test_unit_fl_eop_n     : std_logic;
   signal test_unit_fl_sof_n     : std_logic;
   signal test_unit_fl_eof_n     : std_logic;
   
   signal golden_model_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal golden_model_fl_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal golden_model_fl_src_rdy_n : std_logic;
   signal golden_model_fl_dst_rdy_n : std_logic;
   signal golden_model_fl_sop_n     : std_logic;
   signal golden_model_fl_eop_n     : std_logic;
   signal golden_model_fl_sof_n     : std_logic;
   signal golden_model_fl_eof_n     : std_logic;

   signal sb_rx_data      : std_logic_vector(IFCS*DATA_WIDTH-1 downto 0);
   signal sb_rx_rem       : std_logic_vector(IFCS*DREM_WIDTH-1 downto 0);
   signal sb_rx_src_rdy_n : std_logic_vector(IFCS-1 downto 0);
   signal sb_rx_dst_rdy_n : std_logic_vector(IFCS-1 downto 0);
   signal sb_rx_sop_n     : std_logic_vector(IFCS-1 downto 0);
   signal sb_rx_eop_n     : std_logic_vector(IFCS-1 downto 0);
   signal sb_rx_sof_n     : std_logic_vector(IFCS-1 downto 0);
   signal sb_rx_eof_n     : std_logic_vector(IFCS-1 downto 0);

   signal sb_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sb_tx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal sb_tx_src_rdy_n : std_logic;
   signal sb_tx_dst_rdy_n : std_logic;
   signal sb_tx_sop_n     : std_logic;
   signal sb_tx_eop_n     : std_logic;
   signal sb_tx_sof_n     : std_logic;
   signal sb_tx_eof_n     : std_logic;

   signal reg_rand_bit         : std_logic;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.FL_HW_SCOREBOARD
   generic map (
      IN_DATA_WIDTH        => DATA_WIDTH,
      OUT_DATA_WIDTH       => DATA_WIDTH,
      INTERFACES           => IFCS
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,
      
      -- Input FrameLink Interface
      RX_DATA              => sb_rx_data,
      RX_REM               => sb_rx_rem,
      RX_SOP_N             => sb_rx_sop_n,
      RX_EOP_N             => sb_rx_eop_n,
      RX_SOF_N             => sb_rx_sof_n,
      RX_EOF_N             => sb_rx_eof_n,
      RX_SRC_RDY_N         => sb_rx_src_rdy_n,
      RX_DST_RDY_N         => sb_rx_dst_rdy_n,
    
      -- Output FrameLink Interface
      TX_DATA              => sb_tx_data,
      TX_REM               => sb_tx_rem,
      TX_SOP_N             => sb_tx_sop_n,
      TX_EOP_N             => sb_tx_eop_n,
      TX_SOF_N             => sb_tx_sof_n,
      TX_EOF_N             => sb_tx_eof_n,
      TX_SRC_RDY_N         => sb_tx_src_rdy_n,
      TX_DST_RDY_N         => sb_tx_dst_rdy_n
   );

   sb_rx_data(1*DATA_WIDTH-1 downto 0*DATA_WIDTH)  <= test_unit_fl_data;
   sb_rx_rem (1*DREM_WIDTH-1 downto 0*DREM_WIDTH)  <= test_unit_fl_rem;
   sb_rx_sop_n(0)                                  <= test_unit_fl_sop_n;
   sb_rx_eop_n(0)                                  <= test_unit_fl_eop_n;
   sb_rx_sof_n(0)                                  <= test_unit_fl_sof_n;
   sb_rx_eof_n(0)                                  <= test_unit_fl_eof_n;
   sb_rx_src_rdy_n(0)                              <= test_unit_fl_src_rdy_n;
   test_unit_fl_dst_rdy_n                          <= sb_rx_dst_rdy_n(0);

   sb_rx_data(2*DATA_WIDTH-1 downto 1*DATA_WIDTH)  <= golden_model_fl_data;
   sb_rx_rem (2*DREM_WIDTH-1 downto 1*DREM_WIDTH)  <= golden_model_fl_rem;
   sb_rx_sop_n(1)                                  <= golden_model_fl_sop_n;
   sb_rx_eop_n(1)                                  <= golden_model_fl_eop_n;
   sb_rx_sof_n(1)                                  <= golden_model_fl_sof_n;
   sb_rx_eof_n(1)                                  <= golden_model_fl_eof_n;
   sb_rx_src_rdy_n(1)                              <= golden_model_fl_src_rdy_n;
   golden_model_fl_dst_rdy_n                       <= sb_rx_dst_rdy_n(1);


   -- ----------------------------------------------------

   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;
   
   -- reset generator
   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   -- random bit register for the take signal
   reg_rand_bit_p: process(clk)
      variable seed1, seed2: positive;     -- Seed values for random generator
      variable rand: real;                 -- Random real-number value in range 0 to 1.0
   begin
      if (rising_edge(clk)) then
         UNIFORM(seed1, seed2, rand);
         if (rand > 0.5) then
            reg_rand_bit <= '0';
         else
            reg_rand_bit <= '1';
         end if;
      end if;
   end process;

   sb_tx_dst_rdy_n   <= reg_rand_bit;

   -- the testbench process
   tb: process
   begin

      -- initialisation of signals
      test_unit_fl_data       <= (others => '0');
      test_unit_fl_rem        <= (others => '0');
      test_unit_fl_sof_n      <= '1';
      test_unit_fl_eof_n      <= '1';
      test_unit_fl_sop_n      <= '1';
      test_unit_fl_eop_n      <= '1';
      test_unit_fl_src_rdy_n  <= '1';

      golden_model_fl_data       <= (others => '0');
      golden_model_fl_rem        <= (others => '0');
      golden_model_fl_sof_n      <= '1';
      golden_model_fl_eof_n      <= '1';
      golden_model_fl_sop_n      <= '1';
      golden_model_fl_eop_n      <= '1';
      golden_model_fl_src_rdy_n  <= '1';

      wait for reset_time; 
      wait until rising_edge(clk);

      -- fill the test FIFO
      test_unit_fl_data       <= X"BABABABABABABABA";
      test_unit_fl_rem        <= "000";
      test_unit_fl_sof_n      <= '0';
      test_unit_fl_eof_n      <= '1';
      test_unit_fl_sop_n      <= '0';
      test_unit_fl_eop_n      <= '1';
      test_unit_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      test_unit_fl_data       <= X"ADDAADDAADDAADDA";
      test_unit_fl_rem        <= "101";
      test_unit_fl_sof_n      <= '1';
      test_unit_fl_eof_n      <= '0';
      test_unit_fl_sop_n      <= '1';
      test_unit_fl_eop_n      <= '0';
      test_unit_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      test_unit_fl_data       <= X"0000000015151515";
      test_unit_fl_rem        <= "011";
      test_unit_fl_sof_n      <= '0';
      test_unit_fl_eof_n      <= '0';
      test_unit_fl_sop_n      <= '0';
      test_unit_fl_eop_n      <= '0';
      test_unit_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      test_unit_fl_src_rdy_n  <= '1';

      -- fill the golden model FIFO
      golden_model_fl_data       <= X"BBBABABABABABABA";
      golden_model_fl_rem        <= "000";
      golden_model_fl_sof_n      <= '0';
      golden_model_fl_eof_n      <= '1';
      golden_model_fl_sop_n      <= '0';
      golden_model_fl_eop_n      <= '1';
      golden_model_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      golden_model_fl_data       <= X"0000ADDAADDAADDA";
      golden_model_fl_rem        <= "101";
      golden_model_fl_sof_n      <= '1';
      golden_model_fl_eof_n      <= '0';
      golden_model_fl_sop_n      <= '1';
      golden_model_fl_eop_n      <= '0';
      golden_model_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      golden_model_fl_data       <= X"1515151515151515";
      golden_model_fl_rem        <= "011";
      golden_model_fl_sof_n      <= '0';
      golden_model_fl_eof_n      <= '0';
      golden_model_fl_sop_n      <= '0';
      golden_model_fl_eop_n      <= '0';
      golden_model_fl_src_rdy_n  <= '0';
      wait until rising_edge(clk);

      golden_model_fl_src_rdy_n  <= '1';

      wait until rising_edge(clk);
      wait;
   end process;
end architecture behavioral;
