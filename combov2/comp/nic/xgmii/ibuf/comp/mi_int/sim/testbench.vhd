-- testbench.vhd: Testbench for MI Int
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.ib_sim_oper.all;
use work.ibuf_pkg.all;
use work.lb_pkg.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- Constant declaration
   constant ibuf_clkper       : time := 6.4 ns; 
   constant mi_clkper         : time := 10 ns;
   constant reset_time        : time := 10*mi_clkper;
   constant idle_time         : time := 2*reset_time;

   constant MAC_COUNT         : integer := 16;

   -- Signals declaration
   signal ibuf_clk            : std_logic;
   signal mi_clk              : std_logic;
   signal reset               : std_logic;
   
   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;

   -- MI32 connection between fl_rxbuffer and mi32_sim
   signal mi32_connection      : t_mi32;

   -- Connections to other IBUF components
   signal mi2check_connection    : t_mi2check;
   signal mi2buf_connection      : t_mi2buf;
   signal buf2mi_connection      : t_buf2mi;

   -- CAM Interface
   signal cam_data_in            : std_logic_vector(63 downto 0);
   signal cam_match_en           : std_logic;
   signal cam_match_rst          : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                        MI Int
   -- -------------------------------------------------------------------------
   uut: entity work.mi_int
      generic map (
         MAC_COUNT         => MAC_COUNT
      )
      port map (
         IBUF_CLK          => ibuf_clk,
         RESET             => RESET,
         MI_CLK            => mi_clk,
         MI_DWR      	   => mi32_connection.DWR,
      	MI_ADDR     	   => mi32_connection.ADDR,
      	MI_RD       	   => mi32_connection.RD,
      	MI_WR       	   => mi32_connection.WR,
      	MI_BE       	   => mi32_connection.BE,
      	MI_DRD      	   => mi32_connection.DRD,
      	MI_ARDY     	   => mi32_connection.ARDY,
      	MI_DRDY     	   => mi32_connection.DRDY,
         MI2CHECK          => mi2check_connection,
         MI2BUF            => mi2buf_connection,
         BUF2MI            => buf2mi_connection,
         CAM_DI            => cam_data_in,
         CAM_MATCH_EN      => cam_match_en,
         CAM_MATCH_RST     => cam_match_rst,
         CAM_MATCH_BUS     => open,
         CAM_MATCH_BUS_VLD => open
      );

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim: entity work.MI32_SIM
      generic map (
         UPSTREAM_LOG_FILE   => "./mi32.upstream",
         DOWNSTREAM_LOG_FILE => "./mi32.downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00000100",
         FREQUENCY           => LOCAL_BUS_FREQUENCY,
         BUFFER_EN           => false
      )
      port map (
         -- Common interface
         IB_RESET            => reset,
         IB_CLK              => mi_clk,
   
         -- User Component Interface
         CLK                 => mi_clk,
         MI32                => mi32_connection,
   
         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );

   
   -- ----------------------------------------------------
   -- CLK generator
   ibuf_clkgen: process
   begin
      ibuf_clk <= '1';
      wait for ibuf_clkper/2;
      ibuf_clk <= '0';
      wait for ibuf_clkper/2;
   end process;
   
   mi_clkgen: process
   begin
      mi_clk <= '1';
      wait for mi_clkper/2;
      mi_clk <= '0';
      wait for mi_clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
      begin
         wait until (mi_clk'event and mi_clk='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (mi_clk'event and mi_clk='1');
         mi32_sim_strobe <= '0';
      end ib_op; 


   begin

      -- Buf2Mi data init
      buf2mi_connection.TRFC  <= X"0000000000000010";
      buf2mi_connection.CFC   <= X"0000000000000009";
      buf2mi_connection.DFC   <= X"0000000000000007";
      buf2mi_connection.BODFC <= X"0000000000000001";

      buf2mi_connection.STATUS <= (others => '0');

      -- Cam inputs init
      cam_data_in    <= (others => '0');
      cam_match_en   <= '0';
      cam_match_rst  <= '0';

      -- Wait
      wait for idle_time;

      -- Insert data into CAM
      ib_op(ib_local_write(X"00000088", X"11111111", 1, 16#ABAB#, '0', X"0000000012345678"));
      ib_op(ib_local_write(X"0000008C", X"11111111", 1, 16#ABAB#, '0', X"000000000001AAAA"));

      -- Enable IBUF
      ib_op(ib_local_write(X"00000020", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001"));

      wait for 60*ibuf_clkper;

      -- Try to search inserted CAM
      cam_data_in    <= X"0001AAAA12345678";
      cam_match_en   <= '1';

      wait for ibuf_clkper;
      cam_match_en   <= '0';

      -- Wait
      wait for 5*ibuf_clkper;

      -- Try to search another MAC, not in CAM
      cam_data_in    <= X"0001000011112222";
      cam_match_en   <= '1';

      wait for ibuf_clkper;
      cam_match_en   <= '0';

      -- Head FIFO overflow
      buf2mi_connection.STATUS(0)  <= '1';
      wait for 2*ibuf_clkper;

      -- Only for two periods
      buf2mi_connection.STATUS(0)  <= '0';
      
      wait for 5*ibuf_clkper;
      -- Read status
      ib_op(ib_local_read(X"00000028", X"11111111", 1, 16#ABAB#));

      wait for 10*mi_clkper;
      -- Reset status
      ib_op(ib_local_write(X"00000028", X"11111111", 1, 16#ABAB#, '0', X"0000000000000000"));

      wait for 10*mi_clkper;
      -- Strobe counters
      ib_op(ib_local_write(X"0000002C", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001"));

      wait for 10*mi_clkper;
      -- Reset counters
      ib_op(ib_local_write(X"0000002C", X"11111111", 1, 16#ABAB#, '0', X"0000000000000002"));

      wait for 10*mi_clkper;
      -- Try read from CAM
      ib_op(ib_local_read(X"00000088", X"11111111", 1, 16#ABAB#));
      ib_op(ib_local_read(X"0000008C", X"11111111", 1, 16#ABAB#));

      wait;
   end process;
end architecture behavioral;
