-- testbench.vhd: Testbench for XGMII_IBUF
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
use work.xgmii_pkg.all;
use work.ibuf_pkg.all;
use work.fifo_pkg.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;

use work.lb_pkg.all;
use work.ib_sim_oper.all;

-- use ieee.std_logic_textio.all;
-- use ieee.numeric_std.all;
-- use std.textio.all;

use work.phy_oper.all;

use work.fl_sim_oper.all; -- FrameLink Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant DO_SAMPLING : std_logic := '1';
   constant IFC_COUNT   : integer := 1;

   -- Global Constant Declaration
   constant clkper       : time := 20 ns;
   constant miclkper     : time := 10 ns;
   constant clkper_fl    : time := 10 ns;
   constant clkper_base  : time := 20 ns;
   constant clkper_xgmii : time := 6.4 ns;

   constant PACKETS_DIR  : string := "../../../../../data/packets/common/";
   constant RESET_DELAY        : time := 1 us;

   constant END_DELAY          : time := 10 us;

   constant CTRL_HEADER_EN : boolean := true;
   constant CTRL_FOOTER_EN : boolean := true;
   constant INBANDFCS      : boolean := false;
   constant FRAME_PARTS    : integer := 3;

   constant FL_WIDTH_TX    : integer := 128;
   constant FL_RELAY       : boolean := true;

   constant NUMBER_OF_STAT_BITS  : integer := 6;

   -- Signal declaration
   signal reset         : std_logic;
   signal non_reset     : std_logic;
   signal clk_base      : std_logic;

   -- xgmii interface signals
   signal rxda          : std_logic_vector(31 downto 0);
   signal rxca          : std_logic_vector(3 downto 0);
   signal rxra          : std_logic_vector(3 downto 0);
   signal rxclka        : std_logic;
   signal rxdb          : std_logic_vector(31 downto 0);
   signal rxcb          : std_logic_vector(3 downto 0);
   signal rxrb          : std_logic_vector(3 downto 0);
   signal rxclkb        : std_logic;

   -- ibuf signals
   signal rxclk_out      : std_logic;
   signal xgmii_rxclk    : std_logic;
   signal xgmii_rxd      : std_logic_vector(31 downto 0);
   signal xgmii_rxc      : std_logic_vector(3 downto 0);
   signal int_clk        : std_logic;
   signal sau_valid      : std_logic;
   signal sau_sample     : std_logic;
   signal sau_req        : std_logic;
   signal ctrl_data      : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal ctrl_rem       : std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal ctrl_src_rdy_n : std_logic;
   signal ctrl_header_rdy_n : std_logic;
   signal ctrl_footer_rdy_n : std_logic;
   signal ctrl_sop_n     : std_logic;
   signal ctrl_eop_n     : std_logic;
   signal ctrl_dst_rdy_n : std_logic;
   signal ctrl_req       : std_logic;
   signal ctrl_send      : std_logic;
   signal ctrl_release   : std_logic;
   signal ctrl_rdy       : std_logic;
   signal stat           : t_ibuf_general_stat;
   signal stat_valid     : std_logic;
   signal tx_sof_n       : std_logic;
   signal tx_sop_n       : std_logic;
   signal tx_eop_n       : std_logic;
   signal tx_eof_n       : std_logic;
   signal tx_src_rdy_n   : std_logic;
   signal tx_dst_rdy_n   : std_logic;
   signal tx_data        : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal tx_rem         : std_logic_vector(log2(FL_WIDTH_TX/8)-1 downto 0);
   signal fl_clk         : std_logic;
   signal mi             : t_mi32;
   signal mi_clk         : std_logic;

   -- Control data generator signals
   signal header         : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal footer         : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal cnt_tick       : std_logic_vector(FL_WIDTH_TX-1 downto 0);
   signal mx_ctrl_data_sel : std_logic;
   
   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;

   -- FL Sim RX signals
   signal filename_rx         : t_fl_ctrl;
   signal fl_sim_strobe_rx    : std_logic;
   signal fl_sim_busy_rx      : std_logic;

   -- PHY simulation component signals
   -- Transmit interface
   
   signal phy_sim_tx_clk      : std_logic;
   signal phy_sim_txd         : std_logic_vector(31 downto 0);
   signal phy_sim_txc         : std_logic_vector( 3 downto 0);
   -- Receive interface
   signal phy_sim_rx_clk      : std_logic;
   signal phy_sim_rxd         : std_logic_vector(31 downto 0);
   signal phy_sim_rxc         : std_logic_vector( 3 downto 0);

   type t_oper   is array (0 to (IFC_COUNT - 1)) of t_phy_oper;
   type t_params is array (0 to (IFC_COUNT - 1)) of t_phy_params;
   type t_strobe is array (0 to (IFC_COUNT - 1)) of std_logic;
   type t_busy   is array (0 to (IFC_COUNT - 1)) of std_logic;

   signal phy_oper   : t_oper;
   signal phy_params : t_params;
   signal phy_strobe : t_strobe;
   signal phy_busy   : t_busy;

   signal phy_ctrl   : t_phy_ctrl;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         IBUF
   -- -------------------------------------------------------------------------
   uut: entity work.ibuf_xgmii
      generic map(
         -- Number of items in Data FIFO (64b wide).
         DFIFO_SIZE        => 1024,
         -- Number of items in Header and Footer FIFO (64b wide)
         HFIFO_SIZE        => 128,
         -- Type of the memory used in HFIFO
         HFIFO_MEMTYPE     => LUT,
         -- Enables Frame Headers
         CTRL_HDR_EN       => CTRL_HEADER_EN,
         -- Enables Frame Footer
         CTRL_FTR_EN       => CTRL_FOOTER_EN,
         -- Number of MAC addresses
         MACS              => 16,
         -- Remove FCS from the packet (false -> remove, true -> don't remove)
         INBANDFCS      	=> INBANDFCS,
         -- FrameLink output width (at least 64)
         FL_WIDTH_TX       => FL_WIDTH_TX,
         -- Put FL Relay to the output
         FL_RELAY          => FL_RELAY
      )
      port map(
         -- Common signals
         -- Global reset
         RESET             => reset,
   
         -- XGMII interface
         -- XGMII Receive Clock
         XGMII_RXCLK       => xgmii_rxclk,
         -- XGMII Receive Data
         XGMII_RXD         => xgmii_rxd,
         -- XGMII Receive Control
         XGMII_RXC         => xgmii_rxc,

         -- Internal clock
         -- Clock for SAU and PACODAG component
         INT_CLK           => int_clk,

         -- Sampling unit interface
         -- Request for sampling information
         SAU_REQ           => sau_req,
         -- Accept incoming frame
         SAU_ACCEPT        => sau_sample,
         -- Sampling information valid
         SAU_DV            => sau_valid,
      
         -- Control data generator interface
         -- Control data
         CTRL_DATA         => ctrl_data,
         -- Specifies the number of valid bytes in the last CTRL_DATA beat;
         -- valid only when CTRL_EOP is asserted
         CTRL_REM          => ctrl_rem,
         -- Asserted when the input signals from control data generator are valid
         CTRL_SRC_RDY_N    => ctrl_src_rdy_n,
         -- Signals the start of the incoming control data
         CTRL_SOP_N        => ctrl_sop_n,
         -- Signals the end of the incoming control data
         CTRL_EOP_N        => ctrl_eop_n,
         -- Asserted when data from control data generator will be accepted
         CTRL_DST_RDY_N    => ctrl_dst_rdy_n,
         -- New frame is being received; prepare to generate new control data
         CTRL_REQ          => ctrl_req,
         -- Send control data
         CTRL_SEND         => ctrl_send,
         -- Discard control data
         CTRL_RELEASE      => ctrl_release,
         -- Control data generator is ready to receive new request
         CTRL_RDY          => ctrl_rdy,

           -- Statistic data, active in '1'
         -- MAC address is not accepted
         STAT              => stat,
         -- Statistic is valid
         STAT_VLD          => stat_valid,
  
         -- Output FrameLink inteface
         TX_SOF_N          => tx_sof_n,
         TX_SOP_N          => tx_sop_n,
         TX_EOP_N          => tx_eop_n,
         TX_EOF_N          => tx_eof_n,
         TX_SRC_RDY_N      => tx_src_rdy_n,
         TX_DST_RDY_N      => tx_dst_rdy_n,
         TX_DATA           => tx_data,
         TX_REM            => tx_rem,
         -- Clock for FrameLink interface. Might be asynchronous to IBUF clock
         FL_CLK            => fl_clk,
   
         -- MI32 interface
         MI                => mi,
         -- Clock for MI32 interface
         MI_CLK            => mi_clk
      );

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim: entity work.mi32_sim
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
         MI32                => mi,
   
         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );

     
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - RX
   -- -------------------------------------------------------------------------
   fl_sim_rx: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => FL_WIDTH_TX,
         RX_LOG_FILE    => "fl_sim_rx.txt",
         FRAME_PARTS    => FRAME_PARTS
      )
      port map (
         -- Common interface
         FL_RESET       => RESET,
         FL_CLK         => FL_CLK,
   
         -- FrameLink Interface
         RX_DATA        => tx_data,
         RX_REM         => tx_rem,
         RX_SOF_N       => tx_sof_n,
         RX_EOF_N       => tx_eof_n,
         RX_SOP_N       => tx_sop_n,
         RX_EOP_N       => tx_eop_n,
         RX_SRC_RDY_N   => tx_src_rdy_n,
         RX_DST_RDY_N   => tx_dst_rdy_n,
   
         TX_DATA        => open,
         TX_REM         => open,
         TX_SOF_N       => open,
         TX_EOF_N       => open,
         TX_SOP_N       => open,
         TX_EOP_N       => open,
         TX_SRC_RDY_N   => open,
         TX_DST_RDY_N   => '0',
   
         -- FL SIM interface
         CTRL           => filename_rx,
         STROBE         => fl_sim_strobe_rx,
         BUSY           => fl_sim_busy_rx
      );



   -- -------------------------------------------------------------------------
   --                       PHY SIM XGMII component
   -- -------------------------------------------------------------------------
      phy_sim_xgmii_u: entity work.phy_sim_xgmii
         port map (
            -- TX interface
            TX_CLK       => phy_sim_tx_clk,
            TXD          => phy_sim_txd,
            TXC          => phy_sim_txc,

            -- RX interface
            RX_CLK       => phy_sim_rx_clk,
            RXD          => phy_sim_rxd,
            RXC          => phy_sim_rxc,

            -- Simulation interface
            OPER        => phy_oper(0),
            PARAMS      => phy_params(0),
            STROBE      => phy_strobe(0),
            BUSY        => phy_busy(0)
         );
      
 
   -- ----------------------------------------------------
   -- CLK_BASE clock generator
   clkgen_base : process
   begin
      clk_base <= '1';
      wait for clkper_base/2;
      clk_base <= '0';
      wait for clkper_base/2;
   end process;
   
   -- ----------------------------------------------------
   -- MI clock generator
   clkgen_mi : process
   begin
      mi_clk <= '1';
      wait for miclkper/2;
      mi_clk <= '0';
      wait for miclkper/2;
   end process;
   
   -- ----------------------------------------------------
   -- XGMII clock generator
   clkgen_xgmii : process
   begin
--       rxclka <= '1';
      rxclkb <= '1';
      wait for clkper_xgmii/2;
--       rxclka <= '0';
      rxclkb <= '0';
      wait for clkper_xgmii/2;
   end process;
   
   -- ----------------------------------------------------
   -- FL clock generator
   clkgen_fl : process
   begin
      fl_clk <= '1';
      wait for clkper_fl/2;
      fl_clk <= '0';
      wait for clkper_fl/2;
   end process;
   
   -- ----------------------------------------------------
   -- Reset generation
   proc_reset : process
   begin
      reset <= '1';
      wait for RESET_DELAY;
      reset <= '0';
      wait;
   end process;
   
   non_reset <= not reset;
   
   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------
   
   tb : process
      -- ----------------------------------------------------------------
      --                    Procedures declaration
      -- ----------------------------------------------------------------
  
      -- ----------------------------------------------------------------
      -- Procedure phy_op performs phy operation specified
      -- in data structure t_phy_ctrl
      --
      -- Parameters:
      --       ctrl        - structure for phy controling
      --       id          - interface id
      --       block_wait  - blocking waiting for completion of operation
      --
      procedure phy_op(ctrl : in t_phy_ctrl; id : in integer;
                       block_wait : in boolean := false) is
      begin
         --wait until (phy_busy(id) = '0');
         while (phy_busy(id) /= '0') loop
            wait for 0.1 ns;
         end loop;
         phy_oper(id)   <= ctrl.oper;
         phy_params(id) <= ctrl.params;
         phy_strobe(id) <= '1';
      
         wait until (phy_busy(id) = '1');
         phy_strobe(id)  <= '0';
      
         -- block waiting, if required
         if (block_wait = true) then
            while (phy_busy(id) /= '0') loop
               wait for 0.1 ns;
            end loop;
         end if;
      end phy_op;
   
 
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

 
   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------
   begin

      phy_strobe(0) <= '0';

      -- interface signals init
--       rxda <= X"07070707";
--       rxca <= "1111";
      rxdb <= X"07070707";
      rxcb <= "1111";

      wait for 2*RESET_DELAY;
   
      -- IBUF inicialization
      -- Insert data into CAM
      ib_op(ib_local_write(X"00000080", X"11111111", 1, 16#ABAB#, '0', X"0000000011C9180A"));
      ib_op(ib_local_write(X"00000084", X"11111111", 1, 16#ABAB#, '0', X"0000000000010009"));

      wait for 30*clkper;

      -- Read data from CAM
      ib_op(ib_local_read(X"00000080", X"11111111", 1, 16#ABAB#));
      ib_op(ib_local_read(X"00000084", X"11111111", 1, 16#ABAB#));

      wait for 30*clkper;

      -- Accept MACs from CAM + broadcast + multicast (mode 3)
      ib_op(ib_local_write(X"00000038", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003"));

      wait for 10*clkper; 

      -- Mask all maskable errors
      ib_op(ib_local_write(X"00000024", X"11111111", 1, 16#ABAB#, '0', X"0000000000000000"));

      wait for 10*clkper; 

      -- Set MTU
      ib_op(ib_local_write(X"00000034", X"11111111", 1, 16#ABAB#, '0', X"0000000000000100"));

      wait for 10*clkper; 

      -- Enable IBUF
      ib_op(ib_local_write(X"00000020", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001"));

      wait for 10*clkper; 

      -- Packet reception
--       phy_op(send_tcpdump(PACKETS_DIR & "lo_ack.dump"), 0, false);
--       phy_op(send_tcpdump("../../../../../units/hfe/test/packets/mpls_3pac.dump"), 0, false);
--       wait for 5*clkper;
      phy_op(send_tcpdump_nowait(PACKETS_DIR & "real_1500.dump"), 0, false);

   
   
      wait for END_DELAY; 
   
      wait;
   end process;

   -- ----------------------------------------------------------------
   --                        Interface mapping
   -- ----------------------------------------------------------------
   xgmii_rxd   <= rxda;
   xgmii_rxc   <= rxca;
   xgmii_rxclk <= rxclka;

   rxclka      <= phy_sim_tx_clk;
   rxda        <= phy_sim_txd;
   rxca        <= phy_sim_txc;
   
   -- Sampling control.
   -- We don't have sampling unit yet so this should be enough
   sau_valid <= '1' when sau_req = '1' else '0';
   sau_sample<= DO_SAMPLING when sau_req = '1' else '0';

   -----------------------------------------------------------------------------
   -- Simple control component
   ctrl_rdy       <= not ctrl_dst_rdy_n;
   
   -- cnt_tick counter (auto increment data every cycle)
   cnt_tickp: process(RESET, int_clk)
   begin
      if (RESET = '1') then
         cnt_tick <= (others => '0');
      elsif (int_clk'event AND int_clk = '1') then
         cnt_tick <= cnt_tick + 1;
      end if;
   end process;

   -- Footer data are the one from cnt_tick
   footer         <= cnt_tick;

   -- Create footer from statistic data
   header(FL_WIDTH_TX-1 downto NUMBER_OF_STAT_BITS*8) <= (others => '0');
   header(47 downto 40) <= (others => stat.MAC_CHECK_FAILED);
   header(39 downto 32) <= (others => stat.LEN_BELOW_MIN);
   header(31 downto 24) <= (others => stat.LEN_OVER_MTU);
   header(23 downto 16) <= (others => stat.FRAME_ERROR);
   header(15 downto 8)  <= (others => stat.CRC_CHECK_FAILED);
   header(7 downto 0)   <= (others => stat_valid);

   -- multiplexor mx_ctrl_data
   mx_ctrl_data_sel <= ctrl_header_rdy_n;
   mx_ctrl_datap: process(mx_ctrl_data_sel, header, footer)
   begin
      case mx_ctrl_data_sel is
         when '0' => ctrl_data <= header;
         when '1' => ctrl_data <= footer;
         when others => ctrl_data <= (others => 'X');
      end case;
   end process;

   -- Control signals generation
   ctrl_rem       <= (others => '1');
   ctrl_sop_n     <= '0';
   ctrl_eop_n     <= '0';
   ctrl_src_rdy_n <= ctrl_header_rdy_n and ctrl_footer_rdy_n;

   -- Header is ready when ctrl_send arrives
   ctrl_header_gen: if CTRL_HEADER_EN = true generate
      ctrl_header_rdy_n <= not ctrl_send;
   end generate ctrl_header_gen;

   -- Headers are disabled by generic
   not_ctrl_header_gen: if CTRL_HEADER_EN = false generate
      ctrl_header_rdy_n <= '1';
   end generate not_ctrl_header_gen;

   -- Footer is ready tick after ctrl_send
   ctrl_footer_gen: if CTRL_FOOTER_EN = true generate
      reg_footer_rdy: process(int_clk)
      begin
         if (int_clk'event AND int_clk = '1') then
            ctrl_footer_rdy_n <= not ctrl_send;
         end if;
      end process;
   end generate ctrl_footer_gen;

   -- Footer disabled by generic
   not_ctrl_footer_gen: if CTRL_FOOTER_EN = false generate
      ctrl_footer_rdy_n <= '1';
   end generate not_ctrl_footer_gen;
   
end architecture behavioral;
