-- testbench.vhd: Testbench of timestamp unit entity
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03 at stud.fit.vutbr.cz>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- TODO:
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.lb_pkg.all;
use work.ib_sim_oper.all;  -- Internal bus simulation pkg

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- Global Constant Declaration
   constant period   	   : time := 8 ns; -- 125MHz
   constant reset_delay	   : time := 100 ns;

   -- Address offsets
   constant RTRL  	   : std_logic_vector(31 downto 0) := X"00000000";
   constant RTRH  	   : std_logic_vector(31 downto 0) := X"00000004";
   constant INCRL  	   : std_logic_vector(31 downto 0) := X"00000008";
   constant INCRH  	   : std_logic_vector(31 downto 0) := X"0000000C";

   -- Signal declaration   
   signal clk  	 	   : std_logic := '0';
   signal reset 	   : std_logic;
   
   -- mi32 bus interface
   signal mi32		   : t_mi32;

   -- mi32 simulation signals
   signal mi32_sim_ctrl    : t_ib_ctrl;
   signal mi32_sim_strobe  : std_logic := '0';
   signal mi32_sim_busy    : std_logic;
   
   -- Output interface
   signal ts	   	   : std_logic_vector(63 downto 0);
   signal ts_dv     	   : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         TIMESTAMP UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.ts_unit
      port map(
          CLK          => clk,
          RESET        => reset,
          
	  DWR          => mi32.dwr,
	  ADDR         => mi32.addr,
	  RD           => mi32.rd,
	  WR           => mi32.wr,
	  BE           => mi32.be,
	  DRD          => mi32.drd,
	  ARDY         => mi32.ardy,
	  DRDY	       => mi32.drdy,
          
          TS           => ts,
          TS_DV        => ts_dv
      );

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim_u: entity work.mi32_sim
      generic map(
         UPSTREAM_LOG_FILE   => "", --"./data/mi32upstream",
         DOWNSTREAM_LOG_FILE => "", --"./data/mi32downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00000100",  --01048576
         FREQUENCY           => LOCAL_BUS_FREQUENCY,
         BUFFER_EN           => false
	)

      port map(
         -- Common interface
         IB_RESET          => reset,
         IB_CLK            => clk,

         -- User Component Interface
         CLK		   => clk,
	 MI32.DWR  	   => mi32.dwr,
	 MI32.ADDR 	   => mi32.addr,
	 MI32.RD 	   => mi32.rd,
	 MI32.WR     	   => mi32.wr,
	 MI32.BE    	   => mi32.be,
	 MI32.DRD     	   => mi32.drd,
	 MI32.ARDY  	   => mi32.ardy,
	 MI32.DRDY  	   => mi32.drdy,

         -- IB SIM interface
         STATUS            => open,
         CTRL              => mi32_sim_ctrl,
         STROBE            => mi32_sim_strobe,
         BUSY              => mi32_sim_busy
     );
   

   -- ----------------------------------------------------
   -- CLK generator - 125 MHz
   clk_gen : process
   begin
      clk <= '1';
      wait for period/2;
      clk <= '0';
      wait for period/2;
   end process clk_gen;

   -- ----------------------------------------------------
   -- Reset generation
   proc_reset : process
   begin
      reset <= '1';
      wait for reset_delay;
      reset <= '0';
      wait;
   end process proc_reset;
   
   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------
   tsu_sw_test : process
      -- ----------------------------------------------------------------
      --                    Procedures declaration
      -- ----------------------------------------------------------------

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
	 begin
	    wait until (CLK'event and CLK='1' and mi32_sim_busy = '0');
	    mi32_sim_ctrl <= ctrl;
	    mi32_sim_strobe <= '1';
	    wait until (CLK'event and CLK='1');
	    mi32_sim_strobe <= '0';
	 end ib_op;

       -- ----------------------------------------------------------------
       --                        Testbench Body
       -- ----------------------------------------------------------------
   begin
      wait for reset_delay;

      -- test zapisu do registru
      ib_op(ib_local_write(INCRH, X"11111111", 1, 16#ABAC#, '0', X"AABBCCDDEEFF00FF"));
      ib_op(ib_local_write(INCRL, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EE"));
      ib_op(ib_local_write(RTRL, X"11111111", 4, 16#ABAA#, '0', X"33445566FFFFFFFF"));
      ib_op(ib_local_write(RTRH, X"11111111", 4, 16#ABAB#, '0', X"CCDDEEFF112233AA"));

      wait for 30*period;

      -- test cteni z registru
      ib_op(ib_local_read(RTRH, X"11111111", 4, 16#ABAE#));
      ib_op(ib_local_read(RTRL, X"11111111", 4, 16#ABAF#));

   end process;

end architecture behavioral;
