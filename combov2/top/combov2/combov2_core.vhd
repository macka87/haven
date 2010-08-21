-- combov2_core.vhd : Combov2 NetCOPE core
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.fl_pkg.all;
use work.addr_space.all;

architecture full of COMBOV2_CORE is

component DMA_MOD_2x64b_RXTX is
   port(
      -- ICS Clock (IB and LB)
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- User Clock (FrameLink)
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input interface
      RX0_DATA       : in  std_logic_vector(63 downto 0);
      RX0_DREM       : in  std_logic_vector(2 downto 0);
      RX0_SOF_N      : in  std_logic;
      RX0_EOF_N      : in  std_logic;
      RX0_SOP_N      : in  std_logic;
      RX0_EOP_N      : in  std_logic;
      RX0_SRC_RDY_N  : in  std_logic;
      RX0_DST_RDY_N  : out std_logic;

      RX1_DATA       : in  std_logic_vector(63 downto 0);
      RX1_DREM       : in  std_logic_vector(2 downto 0);
      RX1_SOF_N      : in  std_logic;
      RX1_EOF_N      : in  std_logic;
      RX1_SOP_N      : in  std_logic;
      RX1_EOP_N      : in  std_logic;
      RX1_SRC_RDY_N  : in  std_logic;
      RX1_DST_RDY_N  : out std_logic;

      -- output interfaces
      TX0_DATA       : out std_logic_vector(63 downto 0);
      TX0_DREM       : out std_logic_vector(2 downto 0);
      TX0_SOF_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;

      TX1_DATA       : out std_logic_vector(63 downto 0);
      TX1_DREM       : out std_logic_vector(2 downto 0);
      TX1_SOF_N      : out std_logic;
      TX1_EOF_N      : out std_logic;
      TX1_SOP_N      : out std_logic;
      TX1_EOP_N      : out std_logic;
      TX1_SRC_RDY_N  : out std_logic;
      TX1_DST_RDY_N  : in  std_logic;

      -- Internal Bus
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end component;

component DMA_MOD_2x64b_RXTX_GEN is
   port(
      -- ICS Clock (IB and LB)
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- User Clock (FrameLink)
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input interface
      RX0_DATA       : in  std_logic_vector(63 downto 0);
      RX0_DREM       : in  std_logic_vector(2 downto 0);
      RX0_SOF_N      : in  std_logic;
      RX0_EOF_N      : in  std_logic;
      RX0_SOP_N      : in  std_logic;
      RX0_EOP_N      : in  std_logic;
      RX0_SRC_RDY_N  : in  std_logic;
      RX0_DST_RDY_N  : out std_logic;

      RX1_DATA       : in  std_logic_vector(63 downto 0);
      RX1_DREM       : in  std_logic_vector(2 downto 0);
      RX1_SOF_N      : in  std_logic;
      RX1_EOF_N      : in  std_logic;
      RX1_SOP_N      : in  std_logic;
      RX1_EOP_N      : in  std_logic;
      RX1_SRC_RDY_N  : in  std_logic;
      RX1_DST_RDY_N  : out std_logic;

      -- output interfaces
      TX0_DATA       : out std_logic_vector(63 downto 0);
      TX0_DREM       : out std_logic_vector(2 downto 0);
      TX0_SOF_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;

      TX1_DATA       : out std_logic_vector(63 downto 0);
      TX1_DREM       : out std_logic_vector(2 downto 0);
      TX1_SOF_N      : out std_logic;
      TX1_EOF_N      : out std_logic;
      TX1_SOP_N      : out std_logic;
      TX1_EOP_N      : out std_logic;
      TX1_SRC_RDY_N  : out std_logic;
      TX1_DST_RDY_N  : in  std_logic;

      -- Internal Bus
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end component;

component IB_SWITCH_SLAVE_SYNTH is
port(
   CLK                  : in  std_logic;
   RESET                : in  std_logic;

   PORT0_UP_DATA        : out std_logic_vector(63 downto 0);
   PORT0_UP_SOF_N       : out std_logic;
   PORT0_UP_EOF_N       : out std_logic;
   PORT0_UP_SRC_RDY_N   : out std_logic;
   PORT0_UP_DST_RDY_N   : in  std_logic;
   PORT0_DOWN_DATA      : in  std_logic_vector(63 downto 0);
   PORT0_DOWN_SOF_N     : in  std_logic;
   PORT0_DOWN_EOF_N     : in  std_logic;
   PORT0_DOWN_SRC_RDY_N : in  std_logic;
   PORT0_DOWN_DST_RDY_N : out std_logic;

   PORT1_UP_DATA        : in  std_logic_vector(63 downto 0);
   PORT1_UP_SOF_N       : in  std_logic;
   PORT1_UP_EOF_N       : in  std_logic;
   PORT1_UP_SRC_RDY_N   : in  std_logic;
   PORT1_UP_DST_RDY_N   : out std_logic;
   PORT1_DOWN_DATA      : out std_logic_vector(63 downto 0);
   PORT1_DOWN_SOF_N     : out std_logic;
   PORT1_DOWN_EOF_N     : out std_logic;
   PORT1_DOWN_SRC_RDY_N : out std_logic;
   PORT1_DOWN_DST_RDY_N : in  std_logic;

   PORT2_UP_DATA        : in  std_logic_vector(63 downto 0);
   PORT2_UP_SOF_N       : in  std_logic;
   PORT2_UP_EOF_N       : in  std_logic;
   PORT2_UP_SRC_RDY_N   : in  std_logic;
   PORT2_UP_DST_RDY_N   : out std_logic;
   PORT2_DOWN_DATA      : out std_logic_vector(63 downto 0);
   PORT2_DOWN_SOF_N     : out std_logic;
   PORT2_DOWN_EOF_N     : out std_logic;
   PORT2_DOWN_SRC_RDY_N : out std_logic;
   PORT2_DOWN_DST_RDY_N : in  std_logic
);
end component IB_SWITCH_SLAVE_SYNTH;

component IB_ASFIFO_64B is
   port(
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_RESET       : in  std_logic;

      RX_DATA        : in  std_logic_vector(63 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      TX_DATA        : out std_logic_vector(63 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end component IB_ASFIFO_64B;

component MI32_ASYNC_NOREC is
   port(
      RESET          : in  std_logic;
      -- Master interface
      CLK_M          : in  std_logic;
      MI_M_DWR       : in  std_logic_vector(31 downto 0);
      MI_M_ADDR      : in  std_logic_vector(31 downto 0);
      MI_M_RD        : in  std_logic;
      MI_M_WR        : in  std_logic;
      MI_M_BE        : in  std_logic_vector(3  downto 0);
      MI_M_DRD       : out std_logic_vector(31 downto 0);
      MI_M_ARDY      : out std_logic;
      MI_M_DRDY      : out std_logic;
      -- Slave interface
      CLK_S          : in  std_logic;
      MI_S_DWR       : out std_logic_vector(31 downto 0);
      MI_S_ADDR      : out std_logic_vector(31 downto 0);
      MI_S_RD        : out std_logic;
      MI_S_WR        : out std_logic;
      MI_S_BE        : out std_logic_vector(3  downto 0);
      MI_S_DRD       : in  std_logic_vector(31 downto 0);
      MI_S_ARDY      : in  std_logic;
      MI_S_DRDY      : in  std_logic
   );
end component MI32_ASYNC_NOREC;


-- input buffer for differencial pair
component IBUFDS
port (
   O  : out std_logic;
   I  : in  std_logic;
   IB : in  std_logic
);
end component;

-- output buffer for differencial pair
component OBUFDS
port (
   OB : out std_logic;
   O  : out std_logic;
   I  : in  std_logic
);
end component;

-- output buffer
component OBUF
port (
   O  : out std_logic;
   I  : in  std_logic
);
end component;


-- ----------------------------------------------------------------------------
--                            Signal declaration
-- ----------------------------------------------------------------------------

   -- ------------------------------------------------------------------------
   --                          DMA module signals
   -- ------------------------------------------------------------------------
   -- DMA module buffers FrameLink
   signal swbuf_tx           : t_fl64;
   signal swbuf_rx           : t_fl64;

   -- Interrupts signals
   signal rx_interrupt        : std_logic;
   signal tx_interrupt        : std_logic;
   signal reg_rx_interrupt    : std_logic;
   signal reg_tx_interrupt    : std_logic;
   signal reg_sysmon_alarm    : std_logic;
   signal sysmon_alarm_pulse  : std_logic;
   signal reg_sysmon_alarm_pulse : std_logic;

   signal regasync_link1      : std_logic;
   signal reg_link0           : std_logic;
   signal reg_link1           : std_logic;
   signal link0_change        : std_logic;
   signal link1_change        : std_logic;
   signal reg_link_change    : std_logic;

   signal interrupts          : std_logic_vector(31 downto 0);

   -- ------------------------------------------------------------------------
   --                            Other signals
   -- ------------------------------------------------------------------------

   signal app_mi_dwr         : std_logic_vector(31 downto 0);
   signal app_mi_addr        : std_logic_vector(31 downto 0);
   signal app_mi_rd          : std_logic;
   signal app_mi_wr          : std_logic;
   signal app_mi_be          : std_logic_vector(3 downto 0);
   signal app_mi_drd         : std_logic_vector(31 downto 0);
   signal app_mi_ardy        : std_logic;
   signal app_mi_drdy        : std_logic;
   
   signal MI32_USER_DRD_aux  : std_logic_vector(31 downto 0);
   signal MI32_USER_ARDY_aux : std_logic;
   signal MI32_USER_DRDY_aux : std_logic;
   signal MI32_DMA_DRD_aux   : std_logic_vector(31 downto 0);
   signal MI32_DMA_ARDY_aux  : std_logic;
   signal MI32_DMA_DRDY_aux  : std_logic;
   
   -- attributes to prevent optimization in precision
   attribute dont_touch : string;
   attribute dont_touch of MCLK0_IBUFDS : label is "true";
   attribute dont_touch of MCLK1_IBUFDS : label is "true";
   attribute dont_touch of XCLK0_IBUFDS : label is "true";
   attribute dont_touch of XCLK1_IBUFDS : label is "true";
   attribute dont_touch of GCLK100_IBUFDS : label is "true";
   attribute dont_touch of GCLK250_IBUFDS : label is "true";

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                        USER APPLICATION MODULE
   -- -------------------------------------------------------------------------
   APPLICATION_I : entity work.APPLICATION
   port map(
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESETs
      -- ----------------------------------------------------------------------
      -- Clock signal for user interface
      CLK                     => CLK_USER0,

      -- Global reset
      RESET                   => RESET_USER0,

      -- ----------------------------------------------------------------------
      -- DMA INTERFACE
      -- ----------------------------------------------------------------------
      -- network interfaces interface
      -- input interface
      RX_DATA                => swbuf_tx.DATA,
      RX_DREM                => swbuf_tx.DREM,
      RX_SOF_N               => swbuf_tx.SOF_N,
      RX_EOF_N               => swbuf_tx.EOF_N,
      RX_SOP_N               => swbuf_tx.SOP_N,
      RX_EOP_N               => swbuf_tx.EOP_N,
      RX_SRC_RDY_N           => swbuf_tx.SRC_RDY_N,
      RX_DST_RDY_N           => swbuf_tx.DST_RDY_N,

      -- output interface
      TX_DATA                => swbuf_rx.DATA,
      TX_DREM                => swbuf_rx.DREM,
      TX_SOF_N               => swbuf_rx.SOF_N,
      TX_EOF_N               => swbuf_rx.EOF_N,
      TX_SOP_N               => swbuf_rx.SOP_N,
      TX_EOP_N               => swbuf_rx.EOP_N,
      TX_SRC_RDY_N           => swbuf_rx.SRC_RDY_N,
      TX_DST_RDY_N           => swbuf_rx.DST_RDY_N,

      -- MI32 interface (Slow, efficient)
      MI32_DWR               => app_mi_dwr,
      MI32_ADDR              => app_mi_addr,
      MI32_RD                => app_mi_rd,
      MI32_WR                => app_mi_wr,
      MI32_BE                => app_mi_be,
      MI32_DRD               => app_mi_drd,
      MI32_ARDY              => app_mi_ardy,
      MI32_DRDY              => app_mi_drdy
   );

   
   -- -------------------------------------------------------------------------
   --                              DMA engine
   -- -------------------------------------------------------------------------
   -- DMA_TYPE set in $FW_BASE/pkg/combov2_user_const.vhd
   SZE_DMA_MOD_I: if (DMA_TYPE = "SZE") generate
      DMA_MOD_I : DMA_MOD_2x64b_RXTX
      port map(
         -- Common interface
         CLK            => CLK_ICS,
         RESET          => RESET_ICS,

         USER_CLK       => CLK_USER0,
         USER_RESET     => RESET_USER0,

         RX_INTERRUPT   => rx_interrupt,
         TX_INTERRUPT   => tx_interrupt,

         -- input interface
         RX0_SOF_N       => swbuf_rx.sof_n,
         RX0_SOP_N       => swbuf_rx.sop_n,
         RX0_EOP_N       => swbuf_rx.eop_n,
         RX0_EOF_N       => swbuf_rx.eof_n,
         RX0_SRC_RDY_N   => swbuf_rx.src_rdy_n,
         RX0_DST_RDY_N   => swbuf_rx.dst_rdy_n,
         RX0_DATA        => swbuf_rx.data,
         RX0_DREM        => swbuf_rx.drem,

         RX1_SOF_N       => '0',
         RX1_SOP_N       => '0',
         RX1_EOP_N       => '0',
         RX1_EOF_N       => '0',
         RX1_SRC_RDY_N   => '1',
         RX1_DST_RDY_N   => open,
         RX1_DATA        => (others => '0'),
         RX1_DREM        => (others => '0'),

         -- output interfaces
         TX0_SOF_N       => swbuf_tx.sof_n,
         TX0_SOP_N       => swbuf_tx.sop_n,
         TX0_EOP_N       => swbuf_tx.eop_n,
         TX0_EOF_N       => swbuf_tx.eof_n,
         TX0_SRC_RDY_N   => swbuf_tx.src_rdy_n,
         TX0_DST_RDY_N   => swbuf_tx.dst_rdy_n,
         TX0_DATA        => swbuf_tx.data,
         TX0_DREM        => swbuf_tx.drem,

         TX1_SOF_N       => open,
         TX1_SOP_N       => open,
         TX1_EOP_N       => open,
         TX1_EOF_N       => open,
         TX1_SRC_RDY_N   => open,
         TX1_DST_RDY_N   => '1',
         TX1_DATA        => open,
         TX1_DREM        => open,

         -- Internal Bus
         IB_DOWN_DATA      => IB_DOWN_DATA,
         IB_DOWN_SOF_N     => IB_DOWN_SOF_N,
         IB_DOWN_EOF_N     => IB_DOWN_EOF_N,
         IB_DOWN_SRC_RDY_N => IB_DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N => IB_DOWN_DST_RDY_N,
         IB_UP_DATA        => IB_UP_DATA,
         IB_UP_SOF_N       => IB_UP_SOF_N,
         IB_UP_EOF_N       => IB_UP_EOF_N,
         IB_UP_SRC_RDY_N   => IB_UP_SRC_RDY_N,
         IB_UP_DST_RDY_N   => IB_UP_DST_RDY_N,

         -- MI32 interface
         MI32_DWR          => MI32_DMA_DWR,
         MI32_ADDR         => MI32_DMA_ADDR,
         MI32_RD           => MI32_DMA_RD,
         MI32_WR           => MI32_DMA_WR,
         MI32_BE           => MI32_DMA_BE,
         MI32_DRD          => MI32_DMA_DRD_aux,
         MI32_ARDY         => MI32_DMA_ARDY_aux,
         MI32_DRDY         => MI32_DMA_DRDY_aux
      );
   end generate;
   
   SZE_DMA_MOD_GEN_I: if (DMA_TYPE = "GEN") generate
      DMA_MOD_I : DMA_MOD_2x64b_RXTX_GEN
      port map(
         -- Common interface
         CLK            => CLK_ICS,
         RESET          => RESET_ICS,

         USER_CLK       => CLK_USER0,
         USER_RESET     => RESET_USER0,

         RX_INTERRUPT   => rx_interrupt,
         TX_INTERRUPT   => tx_interrupt,

         -- input interface
         RX0_SOF_N       => swbuf_rx.sof_n,
         RX0_SOP_N       => swbuf_rx.sop_n,
         RX0_EOP_N       => swbuf_rx.eop_n,
         RX0_EOF_N       => swbuf_rx.eof_n,
         RX0_SRC_RDY_N   => swbuf_rx.src_rdy_n,
         RX0_DST_RDY_N   => swbuf_rx.dst_rdy_n,
         RX0_DATA        => swbuf_rx.data,
         RX0_DREM        => swbuf_rx.drem,

         RX1_SOF_N       => '0',
         RX1_SOP_N       => '0',
         RX1_EOP_N       => '0',
         RX1_EOF_N       => '0',
         RX1_SRC_RDY_N   => '1',
         RX1_DST_RDY_N   => open,
         RX1_DATA        => (others => '0'),
         RX1_DREM        => (others => '0'),

         -- output interfaces
         TX0_SOF_N       => swbuf_tx.sof_n,
         TX0_SOP_N       => swbuf_tx.sop_n,
         TX0_EOP_N       => swbuf_tx.eop_n,
         TX0_EOF_N       => swbuf_tx.eof_n,
         TX0_SRC_RDY_N   => swbuf_tx.src_rdy_n,
         TX0_DST_RDY_N   => swbuf_tx.dst_rdy_n,
         TX0_DATA        => swbuf_tx.data,
         TX0_DREM        => swbuf_tx.drem,

         TX1_SOF_N       => open,
         TX1_SOP_N       => open,
         TX1_EOP_N       => open,
         TX1_EOF_N       => open,
         TX1_SRC_RDY_N   => open,
         TX1_DST_RDY_N   => '1',
         TX1_DATA        => open,
         TX1_DREM        => open,

         -- Internal Bus
         IB_DOWN_DATA      => IB_DOWN_DATA,
         IB_DOWN_SOF_N     => IB_DOWN_SOF_N,
         IB_DOWN_EOF_N     => IB_DOWN_EOF_N,
         IB_DOWN_SRC_RDY_N => IB_DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N => IB_DOWN_DST_RDY_N,
         IB_UP_DATA        => IB_UP_DATA,
         IB_UP_SOF_N       => IB_UP_SOF_N,
         IB_UP_EOF_N       => IB_UP_EOF_N,
         IB_UP_SRC_RDY_N   => IB_UP_SRC_RDY_N,
         IB_UP_DST_RDY_N   => IB_UP_DST_RDY_N,

         -- MI32 interface
         MI32_DWR          => MI32_DMA_DWR,
         MI32_ADDR         => MI32_DMA_ADDR,
         MI32_RD           => MI32_DMA_RD,
         MI32_WR           => MI32_DMA_WR,
         MI32_BE           => MI32_DMA_BE,
         MI32_DRD          => MI32_DMA_DRD_aux,
         MI32_ARDY         => MI32_DMA_ARDY_aux,
         MI32_DRDY         => MI32_DMA_DRDY_aux
      );
   end generate;
   
   MI32_DMA_DRD  <= MI32_DMA_DRD_aux;
   MI32_DMA_ARDY <= MI32_DMA_ARDY_aux;
   MI32_DMA_DRDY <= MI32_DMA_DRDY_aux;
   
   
   -- -------------------------------------------------------------------------
   --                                MI ASYNCs
   -- -------------------------------------------------------------------------
   mi_async_app: MI32_ASYNC_NOREC
      port map(
         RESET          => RESET_ICS,
         -- Master interface
         CLK_M          => CLK_ICS,
         MI_M_DWR       => MI32_USER_DWR,
         MI_M_ADDR      => MI32_USER_ADDR,
         MI_M_RD        => MI32_USER_RD,
         MI_M_WR        => MI32_USER_WR,
         MI_M_BE        => MI32_USER_BE,
         MI_M_DRD       => MI32_USER_DRD_aux,
         MI_M_ARDY      => MI32_USER_ARDY_aux,
         MI_M_DRDY      => MI32_USER_DRDY_aux,
         -- Slave interface
         CLK_S          => CLK_USER0,
         MI_S_DWR       => app_mi_dwr,
         MI_S_ADDR      => app_mi_addr,
         MI_S_RD        => app_mi_rd,
         MI_S_WR        => app_mi_wr,
         MI_S_BE        => app_mi_be,
         MI_S_DRD       => app_mi_drd,
         MI_S_ARDY      => app_mi_ardy,
         MI_S_DRDY      => app_mi_drdy
      );
   
   MI32_USER_DRD  <= MI32_USER_DRD_aux;
   MI32_USER_ARDY <= MI32_USER_ARDY_aux;
   MI32_USER_DRDY <= MI32_USER_DRDY_aux;
   
   MI32_NET_DRD  <= (others => '0');
   MI32_NET_ARDY <= '0';
   MI32_NET_DRDY <= '0';
   
   -- -------------------------------------------------------------------------
   -- Interrupt signal handling
   -- No need to reset, because interrupts are ignored for a few cycles
   -- in ID module
   process(CLK_ICS)
   begin
      if CLK_ICS'event and CLK_ICS = '1' then
         reg_rx_interrupt <= rx_interrupt;
         reg_tx_interrupt <= tx_interrupt;

         reg_sysmon_alarm <= SYSMON_ALARM;
         reg_sysmon_alarm_pulse <= sysmon_alarm_pulse;
      end if;
   end process;

   -- Detect rising edge
   sysmon_alarm_pulse <= '1' when (reg_sysmon_alarm='0' and SYSMON_ALARM='1')
                    else '0';

   interrupts <= X"0000000" & 
                 '0' &
                 reg_sysmon_alarm_pulse &
                 reg_tx_interrupt & reg_rx_interrupt ;


   INTERRUPT <= interrupts;
   -- INTR_RDY open -- TODO: deal with INTR_RDY=0, because otherwise
   -- an interrupt may be lost


-- ------------------------------------------------------------------------
-- These signals are unused in NIC, but may be used in other projects
-- ------------------------------------------------------------------------
   -- Clocks
   MCLK0_IBUFDS : IBUFDS
   port map(
      I  => MCLK0_P,
      IB => MCLK0_N,
      O  => open
   );
   MCLK1_IBUFDS : IBUFDS
   port map(
      I  => MCLK1_P,
      IB => MCLK1_N,
      O  => open
   );
   GCLK250_IBUFDS : IBUFDS
   port map(
      I  => GCLK250_P,
      IB => GCLK250_N,
      O  => open
   );
   GCLK100_IBUFDS : IBUFDS
   port map(
      I  => GCLK100_P,
      IB => GCLK100_N,
      O  => open
   );
   XCLK1_IBUFDS : IBUFDS
   port map(
      I  => XCLK1_P,
      IB => XCLK1_N,
      O  => open
   );
   XCLK0_IBUFDS : IBUFDS
   port map(
      I  => XCLK0_P,
      IB => XCLK0_N,
      O  => open
   );

   -- SRAM (no errors reported)

   -- DRAM
   DSCL_OBUF : OBUF
   port map(
      O  => DSCL,
      I  => reset_ics
   );
   DWE_N_OBUF : OBUF
   port map(
      O  => DWE_N,
      I  => reset_ics
   );
   DCAS_N_OBUF : OBUF
   port map(
      O  => DCAS_N,
      I  => reset_ics
   );
   DRAS_N_OBUF : OBUF
   port map(
      O  => DRAS_N,
      I  => reset_ics
   );
   DCK0_P_OBUF : OBUF
   port map(
      O  => DCK0_P,
      I  => reset_ics
   );
   DCK0_N_OBUF : OBUF
   port map(
      O  => DCK0_N,
      I  => reset_ics
   );
   DCK1_P_OBUF : OBUF
   port map(
      O  => DCK1_P,
      I  => reset_ics
   );
   DCK1_N_OBUF : OBUF
   port map(
      O  => DCK1_N,
      I  => reset_ics
   );
   DA_OBUF_GEN: for i in 0 to 13 generate
      DA_OBUF : OBUF
      port map(
         O  => DA(i),
         I  => reset_ics
      );
   end generate;
   DDM_OBUF_GEN: for i in 0 to 7 generate
      DDM_OBUF : OBUF
      port map(
         O  => DDM(i),
         I  => reset_ics
      );
   end generate;
   DBA_OBUF_GEN: for i in 0 to 2 generate
      DBA_OBUF : OBUF
      port map(
         O  => DBA(i),
         I  => reset_ics
      );
   end generate;
   DSA_OBUF_GEN: for i in 0 to 1 generate
      DSA_OBUF : OBUF
      port map(
         O  => DSA(i),
         I  => reset_ics
      );
   end generate;
   DDODT_OBUF_GEN: for i in 0 to 1 generate
      DDODT_OBUF : OBUF
      port map(
         O  => DDODT(i),
         I  => reset_ics
      );
   end generate;
   DCS_N_OBUF_GEN: for i in 0 to 1 generate
      DCS_N_OBUF : OBUF
      port map(
         O  => DCS_N(i),
         I  => reset_ics
      );
   end generate;
   DCKE_OBUF_GEN: for i in 0 to 1 generate
      DCKE_OBUF : OBUF
      port map(
         O  => DCKE(i),
         I  => reset_ics
      );
   end generate;

   -- Misc
   FQTXD_OBUF : OBUF
   port map(
      O  => FQTXD,
      I  => reset_ics
   );
   FQLED_OBUF_GEN: for i in 0 to 3 generate
      FQLED_OBUF : OBUF
      port map(
         O  => FQLED(i),
         I  => reset_ics
      );
   end generate;



end architecture full;

