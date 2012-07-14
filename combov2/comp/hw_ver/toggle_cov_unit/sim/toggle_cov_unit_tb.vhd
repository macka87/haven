-----------------------------------------------------------------------------
-- Project Name: HAVEN
-- File Name:    toggle_cov_unit_tb.vhd
-- Description:  Testbench for the toggle_cov_unit
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         6.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;

use work.math_pack.all;
 
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity testbench is
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of testbench is
-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

constant IN_DATA_WIDTH    : integer := 32;
constant OUT_DATA_WIDTH   : integer := 64;

constant RX_CLKPER        : time := 6 ns;
constant TX_CLKPER        : time := 8 ns;
constant RX_RESET_TIME    : time := 10*RX_CLKPER;
constant TX_RESET_TIME    : time := 10*TX_CLKPER;

constant IN_DATA_WIDTH_MOD: integer := IN_DATA_WIDTH mod 16;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- clocks and resets
signal rx_clk            : std_logic;
signal rx_reset          : std_logic;
signal tx_clk            : std_logic;
signal tx_reset          : std_logic;

-- input data
signal input_data        : std_logic_vector(IN_DATA_WIDTH-1 downto 0);

-- output FrameLink
signal tx_data           : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_rem            : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_sop_n          : std_logic;
signal tx_eop_n          : std_logic;
signal tx_sof_n          : std_logic;
signal tx_eof_n          : std_logic;
signal tx_src_rdy_n      : std_logic;
signal tx_dst_rdy_n      : std_logic;

-- output ready
signal output_ready      : std_logic;

begin

   uut: entity work.toggle_cov_unit
   generic map(
      -- data width
      IN_DATA_WIDTH  => IN_DATA_WIDTH,
      OUT_DATA_WIDTH => OUT_DATA_WIDTH,
      -- the interval between sending coverage report to SW
      SEND_INTERVAL  => 127,
      ENDPOINT_ID    => 255
   )
   port map(
      RX_CLK         => rx_clk,
      RX_RESET       => rx_reset,
      TX_CLK         => tx_clk,
      TX_RESET       => tx_reset,

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input raw interface
      RX_DATA        => input_data,
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        => tx_data,
      TX_REM         => tx_rem,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n,

      -- ------------------ ready signal ------------------------------------
      OUTPUT_READY   => output_ready
   );

   -- RX_CLK generator
   rx_clkgen: process
   begin
      rx_clk <= '1';
      wait for RX_CLKPER/2;
      rx_clk <= '0';
      wait for RX_CLKPER/2;
   end process;

   -- TX_CLK generator
   tx_clkgen: process
   begin
      tx_clk <= '1';
      wait for TX_CLKPER/2;
      tx_clk <= '0';
      wait for TX_CLKPER/2;
   end process;
   
   -- RX_RESET generator
   rx_resetgen: process
   begin
      rx_reset <= '1';
      wait for RX_RESET_TIME;
      rx_reset <= '0';
      wait;
   end process;

   -- TX_RESET generator
   tx_resetgen: process
   begin
      tx_reset <= '1';
      wait for TX_RESET_TIME;
      tx_reset <= '0';
      wait;
   end process;

   -- input data random generator
   input_data_gen_p: process(rx_clk)
      variable seed1, seed2: positive;
      variable rand: real;
      variable int_rand: integer;
      variable stim: std_logic_vector(15 downto 0);
      variable modulus: integer;
   begin
      if (rising_edge(rx_clk)) then
         for i in 0 to IN_DATA_WIDTH/16-1 loop
            UNIFORM(seed1, seed2, rand);               -- generate random number
            int_rand := INTEGER(TRUNC(rand*real(2**16)));  -- rescale 
            stim := std_logic_vector(to_unsigned(int_rand, stim'LENGTH));  

            input_data((i+1)*16-1 downto i*16) <= stim;
         end loop;

         if (IN_DATA_WIDTH_MOD > 0) then
            UNIFORM(seed1, seed2, rand);               -- generate random number
            int_rand := INTEGER(TRUNC(rand*real(2**16)));  -- rescale 
            stim := std_logic_vector(to_unsigned(int_rand, stim'LENGTH));  

            input_data(IN_DATA_WIDTH-1 downto IN_DATA_WIDTH-IN_DATA_WIDTH_MOD) <=
               stim(IN_DATA_WIDTH_MOD-1 downto 0);
         end if;

         input_data(0) <= '0';
         input_data(1) <= '1';
      end if;
   end process;

--   -- output dst_rdy_n random generator
--   tx_dst_rdy_gen_p: process(rx_clk)
--      variable seed1, seed2: positive;
--      variable rand: real;
--   begin
--      if (rising_edge(rx_clk)) then
--         UNIFORM(seed1, seed2, rand);               -- generate random number
--         if (rand < 0.5) then
--            tx_dst_rdy_n <= '0';
--         else
--            tx_dst_rdy_n <= '1';
--         end if;
--      end if;
--   end process;

   --  Output FL_MONITOR
   FL_MONITOR_I : entity work.MONITOR
   generic map (
      RX_TX_DATA_WIDTH => OUT_DATA_WIDTH,
      FILE_NAME  => "./monitor.txt",
      FRAME_PARTS => 1,
      RDY_DRIVER => RND
   )
   port map (
      -- Common interface
      FL_RESET        => tx_reset,
      FL_CLK          => tx_clk,

      RX_DATA         => tx_data,
      RX_REM          => tx_rem,
      RX_SOF_N        => tx_sof_n,
      RX_EOF_N        => tx_eof_n,
      RX_SOP_N        => tx_sop_n,
      RX_EOP_N        => tx_eop_n,
      RX_SRC_RDY_N    => tx_src_rdy_n,
      RX_DST_RDY_N    => tx_dst_rdy_n
   ); 

   stimuli: process
   begin

      wait;
   end process;

end architecture;
