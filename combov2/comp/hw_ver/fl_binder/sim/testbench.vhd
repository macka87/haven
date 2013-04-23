--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   testbench.vhd
--  \date   10-04-2013
--  \brief  Testbench for fl binder

library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

entity testbench is
end entity testbench;

architecture behavioral of testbench is

   -- constants
   constant DATA_WIDTH : integer := 64;
   constant INPUT_COUNT: integer := 3;

   constant clkper     : time := 10 ns; 
   constant reset_time : time := 100 ns;

   -- signals
   signal clk          : std_logic;
   signal reset        : std_logic;

   -- control inputs
   signal HALT         : std_logic;
   signal MEM_DONE     : std_logic;
   signal REGS_DONE    : std_logic;

   -- input framelink - PM - portout monitor
   signal PM_RX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal PM_RX_REM       : std_logic_vector(2 downto 0);
   signal PM_RX_SRC_RDY_N : std_logic;
   signal PM_RX_DST_RDY_N : std_logic;
   signal PM_RX_SOP_N     : std_logic;
   signal PM_RX_EOP_N     : std_logic;
   signal PM_RX_SOF_N     : std_logic;
   signal PM_RX_EOF_N     : std_logic;

   -- input framelink - RM - register file monitor
   signal RM_RX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal RM_RX_REM       : std_logic_vector(2 downto 0);
   signal RM_RX_SRC_RDY_N : std_logic;
   signal RM_RX_DST_RDY_N : std_logic;
   signal RM_RX_SOP_N     : std_logic;
   signal RM_RX_EOP_N     : std_logic;
   signal RM_RX_SOF_N     : std_logic;
   signal RM_RX_EOF_N     : std_logic;

   -- input framelink - MM - memory monitor
   signal MM_RX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal MM_RX_REM       : std_logic_vector(2 downto 0);
   signal MM_RX_SRC_RDY_N : std_logic;
   signal MM_RX_DST_RDY_N : std_logic;
   signal MM_RX_SOP_N     : std_logic;
   signal MM_RX_EOP_N     : std_logic;
   signal MM_RX_SOF_N     : std_logic;
   signal MM_RX_EOF_N     : std_logic;

   -- output framelink
   signal TX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal TX_REM       : std_logic_vector(2 downto 0);
   signal TX_SRC_RDY_N : std_logic;
   signal TX_DST_RDY_N : std_logic;
   signal TX_SOP_N     : std_logic;
   signal TX_EOP_N     : std_logic;
   signal TX_SOF_N     : std_logic;
   signal TX_EOF_N     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut: entity work.FL_BINDER
      generic map (
         DATA_WIDTH   => DATA_WIDTH
      )
      port map (
         CLK          => clk,
         RESET        => reset,

         -- control inputs
         HALT         => HALT,
         MEM_DONE     => MEM_DONE,
         REGS_DONE    => REGS_DONE,

         -- input ifc
         PM_RX_DATA      => PM_RX_DATA,
         PM_RX_REM       => PM_RX_REM,
         PM_RX_SRC_RDY_N => PM_RX_SRC_RDY_N,
         PM_RX_DST_RDY_N => PM_RX_DST_RDY_N,
         PM_RX_SOP_N     => PM_RX_SOP_N,
         PM_RX_EOP_N     => PM_RX_EOP_N,
         PM_RX_SOF_N     => PM_RX_SOF_N,
         PM_RX_EOF_N     => PM_RX_EOF_N,

         RM_RX_DATA      => RM_RX_DATA,
         RM_RX_REM       => RM_RX_REM,
         RM_RX_SRC_RDY_N => RM_RX_SRC_RDY_N,
         RM_RX_DST_RDY_N => RM_RX_DST_RDY_N,
         RM_RX_SOP_N     => RM_RX_SOP_N,
         RM_RX_EOP_N     => RM_RX_EOP_N,
         RM_RX_SOF_N     => RM_RX_SOF_N,
         RM_RX_EOF_N     => RM_RX_EOF_N,

         MM_RX_DATA      => MM_RX_DATA,
         MM_RX_REM       => MM_RX_REM,
         MM_RX_SRC_RDY_N => MM_RX_SRC_RDY_N,
         MM_RX_DST_RDY_N => MM_RX_DST_RDY_N,
         MM_RX_SOP_N     => MM_RX_SOP_N,
         MM_RX_EOP_N     => MM_RX_EOP_N,
         MM_RX_SOF_N     => MM_RX_SOF_N,
         MM_RX_EOF_N     => MM_RX_EOF_N,

         -- output ifc
         TX_DATA      => TX_DATA,
         TX_REM       => TX_REM,
         TX_SRC_RDY_N => TX_SRC_RDY_N,
         TX_DST_RDY_N => TX_DST_RDY_N,
         TX_SOP_N     => TX_SOP_N,
         TX_EOP_N     => TX_EOP_N,
         TX_SOF_N     => TX_SOF_N,
         TX_EOF_N     => TX_EOF_N

      );

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

      wait for reset_time;

      -- initialization
      HALT            <= '0';
      REGS_DONE       <= '0';
      MEM_DONE        <= '0';
      TX_DST_RDY_N    <= '0';

      wait until rising_edge(clk);
      PM_RX_DATA      <= X"1111111111111111";
      PM_RX_REM       <= "111";
      PM_RX_SRC_RDY_N <= '0';
      PM_RX_SOP_N     <= '1';
      PM_RX_EOP_N     <= '1';
      PM_RX_SOF_N     <= '1';
      PM_RX_EOF_N     <= '1';

--      wait until rising_edge(clk);
--      PM_RX_SRC_RDY_N <= '1';
      HALT            <= '1';

      wait until rising_edge(clk);
      RM_RX_DATA      <= X"2222222222222222";
      RM_RX_REM       <= "111";
      RM_RX_SRC_RDY_N <= '0';
      RM_RX_SOP_N     <= '1';
      RM_RX_EOP_N     <= '1';
      RM_RX_SOF_N     <= '1';
      RM_RX_EOF_N     <= '1';

--      wait until rising_edge(clk);
--      RM_RX_SRC_RDY_N <= '1';
      HALT            <= '0';
      REGS_DONE       <= '1';

      wait until rising_edge(clk);
      MM_RX_DATA      <= X"3333333333333333";
      MM_RX_REM       <= "111";
      MM_RX_SRC_RDY_N <= '0';
      MM_RX_SOP_N     <= '1';
      MM_RX_EOP_N     <= '1';
      MM_RX_SOF_N     <= '1';
      MM_RX_EOF_N     <= '1';

--      wait until rising_edge(clk);
--      MM_RX_SRC_RDY_N <= '1';
      REGS_DONE       <= '0';
      MEM_DONE        <= '1';

      wait until rising_edge(clk);
      MEM_DONE       <= '0';
      TX_DST_RDY_N   <= '1';

      wait;

  end process tb; 
   
end architecture behavioral;
