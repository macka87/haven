-- testbench.vhd: Testbench file.
-- Copyright (C) 2007 CESNET
-- Author: Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;


-- Internal bus package
use work.lb_pkg.all;

-- Math package - log2 function
use work.math_pack.all;

-- in_sim Package
use work.ib_sim_oper.all;



entity testbench is
end testbench;



architecture behavioral of testbench is

   constant clkper : time := 13 ns;
   constant lb_clkper : time := 10 ns;
   constant reset_time : time := 30 ns;

   constant PORTS : natural := 3;
   constant INPUTS : natural := 2;
   constant OUTPUTS : natural := 1;


   signal reset : std_logic;

   signal p_rxd  : std_logic_vector((8*PORTS)-1 downto 0);
   signal p_rxdv : std_logic_vector(PORTS-1 downto 0);
   signal p_rxer : std_logic_vector(PORTS-1 downto 0);

   signal p_txd  : std_logic_vector((8*PORTS)-1 downto 0);
   signal p_txen : std_logic_vector(PORTS-1 downto 0);
   signal p_txer : std_logic_vector(PORTS-1 downto 0);

   signal i_rxd  : std_logic_vector((8*INPUTS)-1 downto 0);
   signal i_rxdv : std_logic_vector(INPUTS-1 downto 0);
   signal i_rxer : std_logic_vector(INPUTS-1 downto 0);

   signal o_txd  : std_logic_vector((8*OUTPUTS)-1 downto 0);
   signal o_txen : std_logic_vector(OUTPUTS-1 downto 0);
   signal o_txer : std_logic_vector(OUTPUTS-1 downto 0);

   signal clk : std_logic;
   signal mi32   : t_mi32;
   
   signal mi32_sim_status : t_ib_status;
   signal mi32_sim_ctrl   : t_ib_ctrl;
   signal mi32_sim_strobe : std_logic;
   signal mi32_sim_busy   : std_logic;

begin


   -- UUT instantiation
   uut : entity work.crossbar
      generic map(
         PORTS   => PORTS,
         INPUTS  => INPUTS,
         OUTPUTS => OUTPUTS
      )
   
      port map(
         RESET => reset, -- reset
   
         --*** PORTS INTERFACE ***--
         -- GMII Interface (input ports)
         P_RXD   => p_rxd,      -- RX data
         P_RXDV  => p_rxdv,     -- RX data valid
         P_RXER  => p_rxer,     -- RX error
   
         -- GMII Interface (output ports)
         P_TXD   => p_txd,      -- outGMII transmitt data
         P_TXEN  => p_txen,     -- GMII transmit enable
         P_TXER  => p_txer,     -- GMII transmit error
   
   
         --*** DESIGN INTERFACE ***--
         -- GMII Interface (input)
         I_RXD   => i_rxd,      -- RX data
         I_RXDV  => i_rxdv,     -- RX data valid
         I_RXER  => i_rxer,     -- RX error 
   
         -- GMII Interface (output)
         O_TXD   => o_txd,      -- outGMII transmitt data
         O_TXEN  => o_txen,     -- GMII transmit enable
         O_TXER  => o_txer,     -- GMII transmit error
   
         -- Local Bus Interface
         CLK   => clk,  -- local bus clock
         MI32  => mi32     -- MI32 interface
   
      );
      
      
      -- MI32 sim component instantiation
      Sim_comp : entity work.MI32_SIM
		   generic map(
		      UPSTREAM_LOG_FILE   => "",
		      DOWNSTREAM_LOG_FILE => "",
		      BASE_ADDR           => X"00000000",
		      LIMIT               => conv_std_logic_vector(2000000, 32),
		      FREQUENCY           => 100,
		      BUFFER_EN           => false
		   )
		   port map(
		      -- Common interface
		      IB_RESET          => reset,
		      IB_CLK            => clk,

		      -- User Component Interface
		      CLK           => clk,
		      MI32          => mi32,

		      -- IB SIM interface
		      STATUS            => mi32_sim_status,
		      CTRL              => mi32_sim_ctrl,
		      STROBE            => mi32_sim_strobe,
		      BUSY              => mi32_sim_busy
		  );


   --lb_clock generator
   process
   begin
      clk <= '1';
      wait for lb_clkper/2;
      clk <= '0';
      wait for lb_clkper/2;
   end process;


   --Generating reset
   process
      begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;


   --Ports traffic generator
   process
   begin
      prxdv: for i in 0 to PORTS-1 loop
         p_rxdv <= (others => '0');
         p_rxdv(i) <= '1';
         wait for clkper;
      end loop prxdv;

      p_rxdv <= (others => '0');
      wait for INPUTS*clkper;
   end process;

   process
   begin
      wait for PORTS*clkper;

      irxdv: for i in 0 to INPUTS-1 loop
         i_rxdv <= (others => '0');
         i_rxdv(i) <= '1';
         wait for clkper;
      end loop irxdv;

      i_rxdv <= (others => '0');
   end process;


   process
   begin
      prxer: for i in 0 to PORTS-1 loop
         p_rxer <= (others => '1');
         p_rxer(i) <= '0';
         wait for clkper;
      end loop prxer;

      p_rxer <= (others => '1');
      wait for INPUTS*clkper;
   end process;

   process
   begin
      wait for PORTS*clkper;

      irxer: for i in 0 to INPUTS-1 loop
         i_rxer <= (others => '1');
         i_rxer(i) <= '0';
         wait for clkper;
      end loop irxer;

      i_rxer <= (others => '1');
   end process;


   process
   begin
      prxd: for i in 0 to  PORTS-1 loop
         p_rxd <= (others => '0');
         p_rxd(8*(i+1)-1 downto 8*i) <= X"7e";
         wait for clkper;
      end loop prxd;

      p_rxd <= (others => '0');
      wait for INPUTS*clkper;
   end process;

   process
   begin
      wait for PORTS*clkper;

      irxd: for i in 0 to INPUTS-1 loop
         i_rxd <= (others => '0');
         i_rxd(8*(i+1)-1 downto 8*i) <= X"6f";
         wait for clkper;
      end loop irxd;

      i_rxd <= (others => '0');
   end process;





   -- ------------------------------------------------------------------
   testbench : process
   
   	-- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
      begin
         wait until (clk'event and clk='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (clk'event and clk='1');
         mi32_sim_strobe <= '0';
      end ib_op;

   begin

      wait for reset_time;
      wait for lb_clkper;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000000"));
      wait for 5*lb_clkper;
      ib_op(ib_local_write(X"00000004", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001"));
      wait for 5*lb_clkper;
      ib_op(ib_local_write(X"00000008", X"11111111", 1, 16#ABAB#, '0', X"0000000000000002"));
      wait for 5*lb_clkper;
      ib_op(ib_local_write(X"0000000C", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003"));
      wait for 5*lb_clkper;

      wait for 10*lb_clkper;
      ib_op(ib_local_read(X"00000000", X"00000002", 1, 16#ABAB#));
      wait for 5*lb_clkper;
      ib_op(ib_local_read(X"00000004", X"00000002", 1, 16#ABAB#));
      wait for 5*lb_clkper;
      ib_op(ib_local_read(X"00000008", X"00000002", 1, 16#ABAB#));
      wait for 5*lb_clkper;
      ib_op(ib_local_read(X"0000000C", X"00000002", 1, 16#ABAB#));
      wait;
   end process;

end architecture;
