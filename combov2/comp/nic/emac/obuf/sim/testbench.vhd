-- testbench.vhd: Testbench for EMAC OBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use work.emac_pkg.all;
use work.math_pack.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

use work.lb_pkg.all;
use work.ib_sim_oper.all;

use work.fl_sim_oper.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- Simulation configuration
   constant FLBFM_BEHAVIOR : RDYSignalDriver := RND; -- EVER, ONOFF, RND
   constant FLSIM_SEND_FILE : string := "./fl_sim_send.txt";
   constant INFINITE_PCKTS : boolean := true;

   -- ------------------ Xilinx components ------------------------------------
   -- Clock Buffer
   component BUFG is
      port (
         I : in  std_logic;
         O : out std_logic
      );
   end component;
   
   -- input buffer for differencial pair
   component IBUFDS
   port (
      O  : out std_logic;
      I  : in  std_logic;
      IB : in  std_logic
   );
   end component;

   -- Global Constant Declaration
   constant wrclkper     : time := 10 ns;
   constant clkper_125   : time := 8 ns;

   constant RESET_DELAY  : time := 5 us;

   constant DATA_PATHS   : integer := 2;
   constant INPUT_WIDTH  : integer := DATA_PATHS*8;

   constant DFIFO_SIZE   : integer := 4096;
   constant SFIFO_SIZE   : integer := 128; 
   constant CTRL_CMD     : boolean := false; 
   constant USECLKEN     : boolean := false; 

   constant SFP_MGT_REFCLK_FREQ : integer := 125;
 

   -- Signals -----------------------------------------------------------------
   signal reset                : std_logic;
   signal wr_clk               : std_logic;
   signal adc_clk              : std_logic;

   -- MI32
   signal mi                   : t_mi32;
   
   -- Generic Host Interface
   signal host_clk             : std_logic;
   signal host_opcode          : std_logic_vector(1 downto 0);
   signal host_req             : std_logic;
   signal host_miim_sel        : std_logic;
   signal host_addr            : std_logic_vector(9 downto 0);
   signal host_wr_data         : std_logic_vector(31 downto 0);
   signal host_miim_rdy        : std_logic;
   signal host_rd_data         : std_logic_vector(31 downto 0);
   signal host_emac1_sel       : std_logic;

   -- MAC signals
   signal clk125_o             : std_logic;
   signal clk125_i             : std_logic;

   signal emac0_rx             : t_emac_rx;
   signal emac0_tx             : t_emac_tx;
   signal emac0_control        : t_emac_control;
   signal sfp1_txp             : std_logic;
   signal sfp1_txn             : std_logic;
   signal sfp1_rxp             : std_logic;
   signal sfp1_rxn             : std_logic;
   signal emac0_phyad          : std_logic_vector(4 downto 0);
   signal emac0_resetdone      : std_logic;

   signal emac1_rx             : t_emac_rx;
   signal emac1_tx             : t_emac_tx;
   signal emac1_control        : t_emac_control;
   signal sfp2_txp             : std_logic;
   signal sfp2_txn             : std_logic;
   signal sfp2_rxp             : std_logic;
   signal sfp2_rxn             : std_logic;
   signal emac1_phyad          : std_logic_vector(4 downto 0);
   signal emac1_resetdone      : std_logic;

   signal sfp_mgt_refclkp      : std_logic;
   signal sfp_mgt_refclkn      : std_logic;
   signal clk_ds               : std_logic;

   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;

   -- FL Sim signals
   signal flsim_tx_data       : std_logic_vector(INPUT_WIDTH-1 downto 0);
   signal flsim_tx_rem        :
                           std_logic_vector(log2(INPUT_WIDTH/8) - 1 downto 0);
   signal flsim_tx_sof_n      : std_logic;
   signal flsim_tx_sop_n      : std_logic;
   signal flsim_tx_eop_n      : std_logic;
   signal flsim_tx_eof_n      : std_logic;
   signal flsim_tx_src_rdy_n  : std_logic;
   signal flsim_tx_dst_rdy_n  : std_logic;

   -- EMAC Test Bench Semaphores
   signal emac0_configuration_busy    : boolean := false;
   signal emac0_monitor_finished_1g   : boolean := false;
   signal emac0_monitor_finished_100m : boolean := false;
   signal emac0_monitor_finished_10m  : boolean := false;
   signal emac0_sync_acq_status       : std_logic;

   signal emac1_configuration_busy    : boolean := false;
   signal emac1_monitor_finished_1g   : boolean := false;
   signal emac1_monitor_finished_100m : boolean := false;
   signal emac1_monitor_finished_10m  : boolean := false;
   signal emac1_sync_acq_status       : std_logic;
 
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                         OBUF
   -- -------------------------------------------------------------------------
   uut: entity work.obuf_emac
      generic map(
         DATA_PATHS => DATA_PATHS,
         DFIFO_SIZE => DFIFO_SIZE,
         SFIFO_SIZE => SFIFO_SIZE,
         CTRL_CMD   => CTRL_CMD,
         USECLKEN   => USECLKEN
      )
      port map(
         RESET      => reset,
   
         -- FrameLink input interface
         WRCLK      => wr_clk,
         DATA       => flsim_tx_data,
         DREM       => flsim_tx_rem,
         SRC_RDY_N  => flsim_tx_src_rdy_n,
         SOF_N      => flsim_tx_sof_n,
         SOP_N      => flsim_tx_sop_n,
         EOF_N      => flsim_tx_eof_n,
         EOP_N      => flsim_tx_eop_n,
         DST_RDY_N  => flsim_tx_dst_rdy_n,
   
         -- Transmit interface
         EMAC_CLK       => clk125_i,
         EMAC_CE        => '1',
         TX_EMAC_D              => emac0_tx.D           ,
         TX_EMAC_DVLD           => emac0_tx.DVLD        ,
         TX_EMAC_ACK            => emac0_tx.ACK         ,
         TX_EMAC_FIRSTBYTE      => emac0_tx.FIRSTBYTE   ,
         TX_EMAC_UNDERRUN       => emac0_tx.UNDERRUN    ,
         TX_EMAC_COLLISION      => emac0_tx.COLLISION   ,
         TX_EMAC_RETRANSMIT     => emac0_tx.RETRANSMIT  ,
         TX_EMAC_IFGDELAY       => emac0_tx.IFGDELAY    ,
         TX_EMAC_SPEEDIS10100   => emac0_tx.SPEEDIS10100,
         TX_EMAC_STATS          => emac0_tx.STATS       ,
         TX_EMAC_STATSVLD       => emac0_tx.STATSVLD    ,
         TX_EMAC_STATSBYTEVLD   => emac0_tx.STATSBYTEVLD,
--         TX_EMAC        => emac0_tx,
   
         -- address decoder interface
         ADC_CLK    => adc_clk,
         ADC_RD     => mi.rd,
         ADC_WR     => mi.wr,
         ADC_ADDR   => mi.addr(5 downto 0),
         ADC_DI     => mi.dwr,
         ADC_DO     => mi.drd,
         ADC_DRDY   => mi.drdy
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
         IB_CLK              => adc_clk,
   
         -- User Component Interface
         CLK                 => adc_clk,
         MI32                => mi,
   
         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );

 
   -- -------------------------------------------------------------------------
   --                   FL Simulation Component - TX (FL BFM)
   -- -------------------------------------------------------------------------
   fl_sim_tx: entity work.FL_BFM
      generic map (
         DATA_WIDTH     => INPUT_WIDTH,
         FL_BFM_ID      => 0
      )
      port map (
         -- Common interface
         RESET          => RESET,
         CLK            => wr_clk,

         -- Frame link Interface
         TX_DATA        => flsim_tx_data,
         TX_REM         => flsim_tx_rem,
         TX_SOF_N       => flsim_tx_sof_n,
         TX_EOF_N       => flsim_tx_eof_n,
         TX_SOP_N       => flsim_tx_sop_n,
         TX_EOP_N       => flsim_tx_eop_n,
         TX_SRC_RDY_N   => flsim_tx_src_rdy_n,
         TX_DST_RDY_N   => flsim_tx_dst_rdy_n
      );


   -- -------------------------------------------------------------------------
   --                             MAC Layer
   -- -------------------------------------------------------------------------
   emac_top2_norec: entity work.EMAC_TOP2_NOREC
      port map(
         -- EMAC0 Clocking
         -- 125MHz clock output from transceiver
         CLK125_OUT     => clk125_o,
         -- 125MHz clock input from BUFG
         CLK125         => clk125_i,
   
         -- Client Interface - EMAC0
         -- Client Receiver Interface - EMAC0
         EMAC0_RX_D                    => emac0_rx.D,
         EMAC0_RX_DVLD                 => emac0_rx.DVLD,
         EMAC0_RX_GOODFRAME            => emac0_rx.GOODFRAME,
         EMAC0_RX_BADFRAME             => emac0_rx.BADFRAME,
         EMAC0_RX_FRAMEDROP            => emac0_rx.FRAMEDROP,
         EMAC0_RX_STATS                => emac0_rx.STATS,
         EMAC0_RX_STATSVLD             => emac0_rx.STATSVLD,
         EMAC0_RX_STATSBYTEVLD         => emac0_rx.STATSBYTEVLD,

         -- Client Transmitter Interface - EMAC0
         EMAC0_TX_D                    => emac0_tx.D,
         EMAC0_TX_DVLD                 => emac0_tx.DVLD,
         EMAC0_TX_ACK                  => emac0_tx.ACK,
         EMAC0_TX_FIRSTBYTE            => emac0_tx.FIRSTBYTE,
         EMAC0_TX_UNDERRUN             => emac0_tx.UNDERRUN,
         EMAC0_TX_COLLISION            => emac0_tx.COLLISION,
         EMAC0_TX_RETRANSMIT           => emac0_tx.RETRANSMIT,
         EMAC0_TX_IFGDELAY             => emac0_tx.IFGDELAY,
         EMAC0_TX_STATS                => emac0_tx.STATS,
         EMAC0_TX_STATSVLD             => emac0_tx.STATSVLD,
         EMAC0_TX_STATSBYTEVLD         => emac0_tx.STATSBYTEVLD,

         -- MAC Control Interface - EMAC0
         EMAC0_CONTROL_PAUSEREQ        => emac0_control.PAUSEREQ,
         EMAC0_CONTROL_PAUSEVAL        => emac0_control.PAUSEVAL,

         --EMAC-MGT link status
         EMAC0_CONTROL_SYNCACQSTATUS   => emac0_control.SYNCACQSTATUS,
         -- EMAC0 Interrupt
         EMAC0_CONTROL_ANINTERRUPT     => emac0_control.ANINTERRUPT,
   
         -- Clock Signals - EMAC0
         -- 1000BASE-X PCS/PMA Interface - EMAC0
         TXP_0          => sfp1_txp,
         TXN_0          => sfp1_txn,
         RXP_0          => sfp1_rxp,
         RXN_0          => sfp1_rxn,
         PHYAD_0        => emac0_phyad,
         RESETDONE_0    => emac0_resetdone,

         -- Client Interface - EMAC1
         -- Client Receiver Interface - EMAC1
         EMAC1_RX_D                    => emac1_rx.D,
         EMAC1_RX_DVLD                 => emac1_rx.DVLD,
         EMAC1_RX_GOODFRAME            => emac1_rx.GOODFRAME,
         EMAC1_RX_BADFRAME             => emac1_rx.BADFRAME,
         EMAC1_RX_FRAMEDROP            => emac1_rx.FRAMEDROP,
         EMAC1_RX_STATS                => emac1_rx.STATS,
         EMAC1_RX_STATSVLD             => emac1_rx.STATSVLD,
         EMAC1_RX_STATSBYTEVLD         => emac1_rx.STATSBYTEVLD,

         -- Client Transmitter Interface - EMAC1
         EMAC1_TX_D                    => emac1_tx.D,
         EMAC1_TX_DVLD                 => emac1_tx.DVLD,
         EMAC1_TX_ACK                  => emac1_tx.ACK,
         EMAC1_TX_FIRSTBYTE            => emac1_tx.FIRSTBYTE,
         EMAC1_TX_UNDERRUN             => emac1_tx.UNDERRUN,
         EMAC1_TX_COLLISION            => emac1_tx.COLLISION,
         EMAC1_TX_RETRANSMIT           => emac1_tx.RETRANSMIT,
         EMAC1_TX_IFGDELAY             => emac1_tx.IFGDELAY,
         EMAC1_TX_STATS                => emac1_tx.STATS,
         EMAC1_TX_STATSVLD             => emac1_tx.STATSVLD,
         EMAC1_TX_STATSBYTEVLD         => emac1_tx.STATSBYTEVLD,

         -- MAC Control Interface - EMAC1
         EMAC1_CONTROL_PAUSEREQ        => emac1_control.PAUSEREQ,
         EMAC1_CONTROL_PAUSEVAL        => emac1_control.PAUSEVAL,

         --EMAC-MGT link status
         EMAC1_CONTROL_SYNCACQSTATUS   => emac1_control.SYNCACQSTATUS,
         -- EMAC1 Interrupt
         EMAC1_CONTROL_ANINTERRUPT     => emac1_control.ANINTERRUPT,
   
         -- Clock Signals - EMAC1
         -- 1000BASE-X PCS/PMA Interface - EMAC1
         TXP_1          => sfp2_txp,
         TXN_1          => sfp2_txn,
         RXP_1          => sfp2_rxp,
         RXN_1          => sfp2_rxn,
         PHYAD_1        => emac1_phyad,
         RESETDONE_1    => emac1_resetdone,
         
         -- Generic Host Interface
         HOSTCLK                       => host_clk,
         HOSTOPCODE                    => host_opcode,
         HOSTREQ                       => host_req,
         HOSTMIIMSEL                   => host_miim_sel,
         HOSTADDR                      => host_addr,
         HOSTWRDATA                    => host_wr_data,
         HOSTMIIMRDY                   => host_miim_rdy,
         HOSTRDDATA                    => host_rd_data,
         HOSTEMAC1SEL                  => host_emac1_sel,

         -- 1000BASE-X PCS/PMA RocketIO Reference Clock buffer inputs 
         CLK_DS         => clk_ds,
           
         -- Asynchronous Reset
         RESET          => reset
      );
  

   -- EMAC simulation thingy
   phy0_test: entity work.emac0_phy_tb
      port map (
         clk125m                 => sfp_mgt_refclkp,
         ------------------------------------------------------------------
         -- GMII Interface
         ------------------------------------------------------------------
         txp                     => sfp1_txp,
         txn                     => sfp1_txn,
         rxp                     => sfp1_rxp,
         rxn                     => sfp1_rxn, 
         ------------------------------------------------------------------
         -- Test Bench Semaphores
         ------------------------------------------------------------------
         configuration_busy      => emac0_configuration_busy,
         monitor_finished_1g     => emac0_monitor_finished_1g,
         monitor_finished_100m   => emac0_monitor_finished_100m,
         monitor_finished_10m    => emac0_monitor_finished_10m
      );

   phy1_test: entity work.emac1_phy_tb
      port map (
         clk125m                 => sfp_mgt_refclkp,
         ------------------------------------------------------------------
         -- GMII Interface
         ------------------------------------------------------------------
         txp                     => sfp2_txp,
         txn                     => sfp2_txn,
         rxp                     => sfp2_rxp,
         rxn                     => sfp2_rxn, 
         ------------------------------------------------------------------
         -- Test Bench Semaphores
         ------------------------------------------------------------------
         configuration_busy      => emac1_configuration_busy,
         monitor_finished_1g     => emac1_monitor_finished_1g,
         monitor_finished_100m   => emac1_monitor_finished_100m,
         monitor_finished_10m    => emac1_monitor_finished_10m
      );

   config_test: entity work.configuration_tb
      port map (
         reset                       => reset,
         ------------------------------------------------------------------
         -- Host Interface
         ------------------------------------------------------------------
         host_clk                    => host_clk,
         host_opcode                 => host_opcode,
         host_req                    => host_req,
         host_miim_sel               => host_miim_sel,
         host_addr                   => host_addr,
         host_wr_data                => host_wr_data,
         host_miim_rdy               => host_miim_rdy,
         host_rd_data                => host_rd_data,
         host_emac1_sel              => host_emac1_sel,

         ------------------------------------------------------------------
         -- Test Bench Semaphores
         ------------------------------------------------------------------
         sync_acq_status_0           => emac0_sync_acq_status,
         sync_acq_status_1           => emac1_sync_acq_status,

         emac0_configuration_busy    => emac0_configuration_busy,
         emac0_monitor_finished_1g   => emac0_monitor_finished_1g,
         emac0_monitor_finished_100m => emac0_monitor_finished_100m,
         emac0_monitor_finished_10m  => emac0_monitor_finished_10m,

         emac1_configuration_busy    => emac1_configuration_busy,
         emac1_monitor_finished_1g   => emac1_monitor_finished_1g,
         emac1_monitor_finished_100m => emac1_monitor_finished_100m,
         emac1_monitor_finished_10m  => emac1_monitor_finished_10m 
      );


   -- ----------------------------------------------------
   -- Write clock generator
   wr_clkgen : process
   begin
      wr_clk <= '1';
      wait for wrclkper/2;
      wr_clk <= '0';
      wait for wrclkper/2;
   end process;
 
   -- ----------------------------------------------------
   -- SFP reference clock generator
   sfp_mgt_refclk_p: process
      variable halfcycle   : time := 1 us/(2*SFP_MGT_REFCLK_FREQ);
   begin
      sfp_mgt_refclkp  <= '1';
      sfp_mgt_refclkn  <= '0';
      wait for halfcycle;
      sfp_mgt_refclkp  <= '0';
      sfp_mgt_refclkn  <= '1';
      wait for halfcycle;
   end process;

 
   -- ----------------------------------------------------
   -- Reset generation
--    proc_reset : process
--    begin
--       reset <= '1';
--       wait for RESET_DELAY;
--       reset <= '0';
--       wait;
--    end process;

   -- generate the clock input to the GTP
   -- clk_ds can be shared between multiple MAC instances.
   IBUFDS_MGTCLK : IBUFDS 
      port map (
         I  => sfp_mgt_refclkp,
         IB => sfp_mgt_refclkn,
         O  => clk_ds
      );

   -- 125MHz from transceiver is routed through a BUFG and 
   -- input to the MAC wrappers.
   -- This clock can be shared between multiple MAC instances.
   BUFG_CLK125 : BUFG 
      port map (
         I => clk125_o,
         O => clk125_i
      );

   -- ----------------------------------------------------------------------------
   --                         Main testbench process
   -- ----------------------------------------------------------------------------

   tb : process
   begin
      mi.rd <= '0';
      mi.wr <= '0';
      mi.ardy <= '1';

      emac0_CONTROL.PAUSEREQ     <= '0';
      emac0_CONTROL.PAUSEVAL     <= (others => '0');
      emac1_CONTROL.PAUSEREQ     <= '0';
      emac1_CONTROL.PAUSEVAL     <= (others => '0');
      wait;
   end process;

   -- Generate FL input
   flgenp: process
   begin
      wait for RESET_DELAY;

      -- Generate FL input
      SendWriteFile(FLSIM_SEND_FILE, FLBFM_BEHAVIOR, flCmd_0, 0);

      if INFINITE_PCKTS = false then
         wait;
      end if;
   end process;

end architecture behavioral;
