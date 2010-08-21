-- testbench.vhd: Testbench of timestamp unit entity
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

--library unisim;
--use unisim.vcomponents.all;

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
   constant mi32_period    : time := 8  ns; -- 125MHz
   constant combov2_ref_period : time := 6.4  ns; -- 156.25MHz
   constant ptm_precise_period : time := 6.25  ns; -- 160MHz
   constant pps_period 	   : time := 1  us; --  1Hz
   constant reset_delay	   : time := 100 ns;

   -- Address offsets							  
   constant MICOM_LOW  	   : std_logic_vector(31 downto 0) := X"00000000";
   constant MICOM_MIDDLE   : std_logic_vector(31 downto 0) := X"00000004";
   constant MICOM_HIGH 	   : std_logic_vector(31 downto 0) := X"00000008";
   constant CNTRL  	   : std_logic_vector(31 downto 0) := X"0000000C";
   constant DETECT_PPS_N   : std_logic_vector(31 downto 0) := X"00000010";
   constant INTA	   : std_logic_vector(31 downto 0) := X"00000014";
   constant SEL_PPS_N	   : std_logic_vector(31 downto 0) := X"00000018";
   constant FREQ_REG       : std_logic_vector(31 downto 0) := X"0000001C";

   -- Signal declaration   
   signal mi32_clk          : std_logic := '0';
   signal mi32_reset        : std_logic;
   signal combov2_ref_clk   : std_logic := '0';
   signal combov2_ref_reset : std_logic;
   signal reg_combov2_ref_reset : std_logic;
   signal ptm_precise_clk   : std_logic := '0';
   signal ptm_precise_reset : std_logic;
   signal reg_ptm_precise_reset : std_logic;
   
   -- mi32 bus interface
   signal mi32		   : t_mi32;

   -- mi32 simulation signals
   signal mi32_sim_ctrl    : t_ib_ctrl;
   signal mi32_sim_strobe  : std_logic := '0';
   signal mi32_sim_busy    : std_logic;
   
   -- Output interface
   signal ts	   	   : std_logic_vector(63 downto 0);
   signal ts_dv     	   : std_logic;
   signal ts_clk           : std_logic;

   -- Input GPS signal
   signal gps_pps_n	   : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         TIMESTAMP UNIT
   -- -------------------------------------------------------------------------
   uut : entity work.tsu_cv2
      generic map(
         TS_MULT_USE_DSP              => false,
         COMBOV2_REF_CLK_FREQUENCY    => 125000, -- frequency of combov2 clk
         PTM_PRECISE_CLK_FREQUENCY    => 134000 -- frequency of ptm precise crystal clk
      )
      port map(
          -- Combo clock and reset signals for MI_32 interface
          MI32_CLK       => mi32_clk,
          MI32_RESET     => mi32_reset,
          
          -- In / Out SW interface via MI_32
	  DWR          => mi32.dwr,
	  ADDR         => mi32.addr,
	  RD           => mi32.rd,
	  WR           => mi32.wr,
	  BE           => mi32.be,
	  DRD          => mi32.drd,
	  ARDY         => mi32.ardy,
	  DRDY	       => mi32.drdy,
          
          -- Input PPS_N signal from GPS
          GPS_PPS_N    => gps_pps_n,

          -- -------------------------------------------
          -- TSU core clock ----------------------------
          -- -------------------------------------------
          -- COMBOv2 base clock
          COMBOV2_REF_CLK   => combov2_ref_clk,
          COMBOV2_REF_RESET => combov2_ref_reset,
          -- PTM precise crystal clock
          PTM_PRECISE_CLK   => ptm_precise_clk,
          PTM_PRECISE_RESET => ptm_precise_reset,

          -- Output pacodag interface
          TS_CLK       => ts_clk,
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
         LIMIT               => X"00000300",  --01048576
         FREQUENCY           => LOCAL_BUS_FREQUENCY,
         BUFFER_EN           => true
	)

      port map(
         -- Common interface
         IB_RESET          => mi32_reset,
         IB_CLK            => mi32_clk,

         -- User Component Interface
         CLK		   => mi32_clk,
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
   mi32_clk_gen : process
   begin
      mi32_clk <= '1';
      wait for mi32_period/2;
      mi32_clk <= '0';
      wait for mi32_period/2;
   end process;

   -- ----------------------------------------------------
   -- COMBOV2_REF_CLK generator - 156.25 MHz
   combov2_ref_clk_gen : process
   begin
      combov2_ref_clk <= '1';
      wait for combov2_ref_period/2;
      combov2_ref_clk <= '0';
      wait for combov2_ref_period/2;
   end process;

   -- ----------------------------------------------------
   -- PTM_PRECISE_CLK generator - 160 MHz
   ptm_precise_clk_gen : process
   begin
      ptm_precise_clk <= '1';
      wait for ptm_precise_period/2;
      ptm_precise_clk <= '0';
      wait for ptm_precise_period/2;
   end process;

   -- ----------------------------------------------------
   -- MI32 Reset generation
   proc_mi32_reset : process
   begin
      mi32_reset <= '1';
      wait for reset_delay;
      mi32_reset <= '0';
      wait;
   end process;
  
   -- ----------------------------------------------------
   -- COMBOV2_REF Reset generation
   proc_combov2_ref_reset : process(combov2_ref_clk)
   begin
      if combov2_ref_clk'event and combov2_ref_clk = '1' then
         combov2_ref_reset <= reg_combov2_ref_reset;
         reg_combov2_ref_reset <= mi32_reset;
      end if; 
   end process;
  
   -- ----------------------------------------------------
   -- PTM_PRECISE Reset generation
   proc_ptm_precise_reset : process(ptm_precise_clk)
   begin
      if ptm_precise_clk'event and ptm_precise_clk = '1' then
         ptm_precise_reset <= reg_ptm_precise_reset;
         reg_ptm_precise_reset <= mi32_reset;
      end if; 
   end process;
  
   -- ----------------------------------------------------
   -- PPS_N pulse generator
   pps_gen : process
   begin
      gps_pps_n <= '1';
      wait for 9*pps_period/10;
      gps_pps_n <= '0';
      wait for pps_period/10;
   end process;

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
	    wait until (mi32_clk'event and mi32_clk='1' and mi32_sim_busy = '0');
	    mi32_sim_ctrl <= ctrl;
	    mi32_sim_strobe <= '1';
	    wait until (mi32_clk'event and mi32_clk='1');
	    mi32_sim_strobe <= '0';
	 end ib_op;

       -- ----------------------------------------------------------------
       --                        Testbench Body
       -- ----------------------------------------------------------------
   begin
      wait for reset_delay;

      -- write into register INCR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FF"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 1, 16#ABAD#, '0', X"11223344556677EE"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000000"));

      -- write into register RTR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FA"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EB"));
      ib_op(ib_local_write(MICOM_HIGH, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EC"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000001"));

      -- write into register RTR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FD"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EE"));
      ib_op(ib_local_write(MICOM_HIGH, X"11111111", 4, 16#ABAD#, '0', X"11223344556677EF"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000001"));

      -- write into register INTA
      ib_op(ib_local_write(INTA, X"11111111", 1, 16#ABAA#, '0', X"0000000000000001"));

      -- read from register RTR
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000005"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_HIGH, X"11111111", 4, 16#ABAB#));

      -- read from register PPS
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000007"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));
      ib_op(ib_local_read(MICOM_HIGH, X"11111111", 4, 16#ABAB#));

      -- read from register INCR
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000004"));
      ib_op(ib_local_read(MICOM_LOW, X"11111111", 4, 16#ABAB#, true));
      ib_op(ib_local_read(MICOM_MIDDLE, X"11111111", 4, 16#ABAB#));

      -- write into register INCR
      ib_op(ib_local_write(MICOM_LOW, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF00FC"));
      ib_op(ib_local_write(MICOM_MIDDLE, X"11111111", 1, 16#ABAD#, '0', X"11223344556677DE"));
      ib_op(ib_local_write(CNTRL, X"11111111", 4, 16#ABAA#, '0', X"0000000000000000"));

      -- write into register INTA
      ib_op(ib_local_write(INTA, X"11111111", 1, 16#ABAA#, '0', X"0000000000000000"));

      -- read from register FREQ_REG
      ib_op(ib_local_read(FREQ_REG, X"11111111", 4, 16#ABAB#));

      -- read from register DETECT_PPS_N
      ib_op(ib_local_read(DETECT_PPS_N, X"11111111", 4, 16#ABAB#));

      -- write into register SEL_PPS_N
      ib_op(ib_local_write(SEL_PPS_N, X"11111111", 4, 16#ABAC#, '0', X"AABBCCDDEEFF0001"));

      wait for 30*mi32_period;

   end process;

end architecture behavioral;
