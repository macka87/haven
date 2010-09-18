-- mi_splitter_ondriks_tb: Testbench for Ondrik's MI splitter
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;



-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

-- -----------------------Testbench constant-----------------------------------
   constant clkper          : time    := 10 ns;
   constant reset_time      : time    := 10 * clkper;

-- -----------------------Testbench auxilarity signals-------------------------
   -- CLK_GEN Signals
   signal reset     : std_logic;
   signal clk       : std_logic;
   
   -- MI32 interface for splitter
   signal mi_splitter_dwr      : std_logic_vector(31 downto 0);
   signal mi_splitter_addr     : std_logic_vector(31 downto 0);
   signal mi_splitter_rd       : std_logic;
   signal mi_splitter_wr       : std_logic;
   signal mi_splitter_be       : std_logic_vector(3 downto 0);
   signal mi_splitter_drd      : std_logic_vector(31 downto 0);
   signal mi_splitter_ardy     : std_logic;
   signal mi_splitter_drdy     : std_logic;

   -- MI32 interface for watches
   signal mi_watch_dwr         : std_logic_vector(31 downto 0);
   signal mi_watch_addr        : std_logic_vector(31 downto 0);
   signal mi_watch_rd          : std_logic;
   signal mi_watch_wr          : std_logic;
   signal mi_watch_be          : std_logic_vector(3 downto 0);
   signal mi_watch_drd         : std_logic_vector(31 downto 0);
   signal mi_watch_ardy        : std_logic;
   signal mi_watch_drdy        : std_logic;

   -- MI32 interface for stats
   signal mi_stat_dwr          : std_logic_vector(31 downto 0);
   signal mi_stat_addr         : std_logic_vector(31 downto 0);
   signal mi_stat_rd           : std_logic;
   signal mi_stat_wr           : std_logic;
   signal mi_stat_be           : std_logic_vector(3 downto 0);
   signal mi_stat_drd          : std_logic_vector(31 downto 0);
   signal mi_stat_ardy         : std_logic;
   signal mi_stat_drdy         : std_logic;

   -- MI32 interface for verification core
   signal mi_ver_dwr           : std_logic_vector(31 downto 0);
   signal mi_ver_addr          : std_logic_vector(31 downto 0);
   signal mi_ver_rd            : std_logic;
   signal mi_ver_wr            : std_logic;
   signal mi_ver_be            : std_logic_vector(3 downto 0);
   signal mi_ver_drd           : std_logic_vector(31 downto 0);
   signal mi_ver_ardy          : std_logic;
   signal mi_ver_drdy          : std_logic;

   -- MI32 splitter output
   signal mi_spl_out_dwr        : std_logic_vector(95 downto 0);
   signal mi_spl_out_addr       : std_logic_vector(95 downto 0);
   signal mi_spl_out_rd         : std_logic_vector(2 downto 0);
   signal mi_spl_out_wr         : std_logic_vector(2 downto 0);
   signal mi_spl_out_be         : std_logic_vector(11 downto 0);
   signal mi_spl_out_drd        : std_logic_vector(95 downto 0);
   signal mi_spl_out_ardy       : std_logic_vector(2 downto 0);
   signal mi_spl_out_drdy       : std_logic_vector(2 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- Reset generation -----------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
   -- clk generator ------------------------------------------------------------
   clk_gen : process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   -- -------------------------------------------------------------------------
   -- MI Splitter Ondrik's
   -- -------------------------------------------------------------------------
   uut: entity work.MI_SPLITTER_ONDRIKS
   generic map(
      -- Data width
      DATA_WIDTH    => 32,
      -- Number of output ports
      ITEMS         => 3,

      -- ADDRESS SPACE

      -- PORT0: 0x00080000 -- 0x00080FFF
      PORT0_BASE    => X"00080000",
      PORT0_LIMIT   => X"00001000",
      -- PORT1: 0x00081000 -- 0x00081FFF
      PORT1_BASE    => X"00081000",
      PORT1_LIMIT   => X"00001000",
      -- PORT2: 0x01000000 -- 0x01FFFFFF
      PORT2_BASE    => X"01000000",
      PORT2_LIMIT   => X"01000000",

      -- Input pipeline
      PIPE          => false,
      PIPE_OUTREG   => false
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK         => CLK,
      RESET       => RESET,
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      => mi_splitter_dwr,
      IN_ADDR     => mi_splitter_addr,
      IN_BE       => mi_splitter_be,
      IN_RD       => mi_splitter_rd,
      IN_WR       => mi_splitter_wr,
      IN_ARDY     => mi_splitter_ardy,
      IN_DRD      => mi_splitter_drd,
      IN_DRDY     => mi_splitter_drdy,
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     => mi_spl_out_dwr,
      OUT_ADDR    => mi_spl_out_addr,
      OUT_BE      => mi_spl_out_be,
      OUT_RD      => mi_spl_out_rd,
      OUT_WR      => mi_spl_out_wr,
      OUT_ARDY    => mi_spl_out_ardy,
      OUT_DRD     => mi_spl_out_drd,
      OUT_DRDY    => mi_spl_out_drdy
   );

   mi_watch_dwr       <= mi_spl_out_dwr(31 downto 0);
   mi_watch_addr      <= mi_spl_out_addr(31 downto 0);
   mi_watch_be        <= mi_spl_out_be(3 downto 0);
   mi_watch_rd        <= mi_spl_out_rd(0);
   mi_watch_wr        <= mi_spl_out_wr(0);

   mi_stat_dwr        <= mi_spl_out_dwr(63 downto 32);
   mi_stat_addr       <= mi_spl_out_addr(63 downto 32);
   mi_stat_be         <= mi_spl_out_be(7 downto 4);
   mi_stat_rd         <= mi_spl_out_rd(1);
   mi_stat_wr         <= mi_spl_out_wr(1);

   mi_ver_dwr         <= mi_spl_out_dwr(95 downto 64);
   mi_ver_addr        <= mi_spl_out_addr(95 downto 64);
   mi_ver_be          <= mi_spl_out_be(11 downto 8);
   mi_ver_rd          <= mi_spl_out_rd(2);
   mi_ver_wr          <= mi_spl_out_wr(2);

   mi_spl_out_drd     <= mi_ver_drd  & mi_stat_drd  & mi_watch_drd;
   mi_spl_out_ardy    <= mi_ver_ardy & mi_stat_ardy & mi_watch_ardy;
   mi_spl_out_drdy    <= mi_ver_drdy & mi_stat_drdy & mi_watch_drdy;


   tb : process
   begin

      mi_watch_drd  <= (others => '0');
      mi_watch_ardy <= '1';
      mi_watch_drdy <= '0';

      mi_stat_drd  <= (others => '0');
      mi_stat_ardy <= '1';
      mi_stat_drdy <= '0';

      mi_ver_drd  <= (others => '0');
      mi_ver_ardy <= '1';
      mi_ver_drdy <= '0';

      mi_splitter_dwr  <= (others => '0');
      mi_splitter_addr <= (others => '0');
      mi_splitter_be   <= "1111";
      mi_splitter_rd   <= '0';
      mi_splitter_wr   <= '0';

      -- wait for reset time
      wait for reset_time;

      mi_splitter_addr <= X"00081000";
      mi_splitter_rd   <= '1';

      wait for clkper;

      mi_splitter_addr <= (others => '0');
      mi_splitter_rd   <= '0';

      wait;
   end process;
end architecture behavioral;
