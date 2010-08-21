-- dma_ctrl_arch.vhd: dma control block entity
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
-- TODO:
-- KEYWORDS : TODO, DEBUG
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture pac_behav of pac_dma_ctrl is
      -- Chipscope ICON
   component icon3 is
      port (  
              CONTROL0 : inout std_logic_vector(35 downto 0);
              CONTROL1 : inout std_logic_vector(35 downto 0);
              CONTROL2 : inout std_logic_vector(35 downto 0)
           );
   end component; 

   -- Chipscope ILA (144-bit trigger port)
   component ila144 is
      port (  
              CONTROL : inout std_logic_vector(35 downto 0);
              CLK     : in std_logic;
              TRIG0   : in std_logic_vector(143 downto 0)
           );
   end component;

   -- Chipscope signals
   signal control0            : std_logic_vector(35 downto 0);
   signal control1            : std_logic_vector(35 downto 0);
   signal control2            : std_logic_vector(35 downto 0);
   signal ila144_trig0        : std_logic_vector(143 downto 0);
   signal ila144_trig1        : std_logic_vector(143 downto 0);
   signal ila144_trig2        : std_logic_vector(143 downto 0);

   attribute noopt : boolean;
   attribute dont_touch : boolean;

   attribute noopt of icon3    : component is TRUE;
   attribute noopt of ila144   : component is TRUE;
   attribute dont_touch of icon3    : component is TRUE;
   attribute dont_touch of ila144   : component is TRUE;


   constant BLOCK_SIZE : integer := 16;
   constant DMA_DATA_WIDTH : integer := 32; -- 128/4

   constant DDM_DMA_ID : std_logic_vector(1 downto 0) := "00";
   constant SUM_DMA_ID : std_logic_vector(1 downto 0) := "01";
   constant RX_DMA_ID  : std_logic_vector(1 downto 0) := "10";
   constant TX_DMA_ID  : std_logic_vector(1 downto 0) := "11";

   -- PAC* constants defined in pac_dma_pkg.vhd
   constant DDM_IB_BASE : std_logic_vector(31 downto 0) := PAC_IB_BASE;
   constant SUM_IB_BASE : std_logic_vector(31 downto 0) := PAC_IB_BASE;

   constant RX_BUFFER_ADDR : std_logic_vector(31 downto 0) := PAC_RX_BUFF_BASE;
   constant RX_BUFFER_GAP  : std_logic_vector(31 downto 0) := PAC_RX_BUFF_GAP;
   constant RX_BUFFER_SIZE : integer := PAC_RX_BUFF_SIZE;

   constant TX_BUFFER_ADDR : std_logic_vector(31 downto 0) := PAC_TX_BUFF_BASE;
   constant TX_BUFFER_GAP  : std_logic_vector(31 downto 0) := PAC_TX_BUFF_GAP;
   constant TX_BUFFER_SIZE : integer := PAC_TX_BUFF_SIZE;

   constant RF_NFIFO_BLOCK_SIZE : integer := BLOCK_SIZE;
   constant RF_NFIFO_LUT_MEMORY : boolean := false;
   constant RF_NFIFO_OUTPUT_REG : boolean := false;

   signal ddm_dma_addr     : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal ddm_dma_dout     : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal ddm_dma_req      : std_logic;
   signal ddm_dma_ack      : std_logic;
   signal ddm_dma_done     : std_logic;
   signal ddm_dma_tag      : std_logic_vector(15 downto 0);

   signal ddm_run          : std_logic_vector(2*IFCS-1 downto 0);
   signal ddm_init         : std_logic_vector(2*IFCS-1 downto 0);
   signal ddm_idle         : std_logic_vector(2*IFCS-1 downto 0);
   signal sum_idle         : std_logic_vector(2*IFCS-1 downto 0);
   signal sum_flush        : std_logic_vector(2*IFCS-1 downto 0);
   signal ctrl_idle        : std_logic_vector(2*IFCS-1 downto 0);

   signal rx_run          : std_logic_vector(IFCS-1 downto 0);
   signal tx_run          : std_logic_vector(IFCS-1 downto 0);
   signal rx_idle         : std_logic_vector(IFCS-1 downto 0);
   signal tx_idle         : std_logic_vector(IFCS-1 downto 0);

   signal ddm_rf_addr       : std_logic_vector(log2(IFCS)-1 downto 0);
   signal ddm_rf_data       : std_logic_vector(log2(BLOCK_SIZE) + 64 downto 0);
   signal ddm_rf_data_vld   : std_logic;
   signal ddm_rf_full       : std_logic_vector(IFCS-1 downto 0);
   signal ddm_rf_init       : std_logic_vector(IFCS-1 downto 0);

     -- Rx nfifo to rx_dma_ctrl
   signal rx_nfifo_dout     : std_logic_vector(63 downto 0);
   signal rx_nfifo_dout_vld : std_logic;
   signal rx_nfifo_raddr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rx_nfifo_rd       : std_logic;
   signal rx_nfifo_empty    : std_logic_vector(IFCS-1 downto 0);

      -- Tx nfifo to tx_dma_ctrl
   signal tx_nfifo_dout     : std_logic_vector(63 downto 0);
   signal tx_nfifo_dout_vld : std_logic;
   signal tx_nfifo_raddr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal tx_nfifo_rd       : std_logic;
   signal tx_nfifo_empty    : std_logic_vector(IFCS-1 downto 0);

   signal sum_dma_addr      : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal sum_dma_dout      : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal sum_dma_req       : std_logic;
   signal sum_dma_ack       : std_logic;
   signal sum_dma_done      : std_logic;
   signal sum_dma_tag       : std_logic_vector(15 downto 0);

   -- RxReqFifo interface
   signal sum_rf_raddr   : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal sum_rf_dout    : std_logic_vector(log2(BLOCK_SIZE) + 64 downto 0);
   signal sum_rf_dvld    : std_logic;
   signal sum_rf_empty   : std_logic_vector(IFCS-1 downto 0);
   signal sum_rf_read    : std_logic;
   signal sum_rf_status  : std_logic_vector(log2(BLOCK_SIZE+1)*IFCS-1 downto 0);

   -- Rx status update
   signal rx_su_addr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal rx_su_data    : std_logic_vector(NUM_FLAGS+16-1 downto 0);
   signal rx_su_dvld    : std_logic;
   signal rx_su_hfull   : std_logic_vector(IFCS-1 downto 0);

   -- Tx status update
   signal tx_su_addr    : std_logic_vector(abs(log2(IFCS)-1) downto 0);
   signal tx_su_data    : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal tx_su_dvld    : std_logic;
   signal tx_su_hfull   : std_logic_vector(IFCS-1 downto 0);

   signal rx_dma_addr  : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal rx_dma_dout  : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal rx_dma_req   : std_logic;
   signal rx_dma_ack   : std_logic;
   signal rx_dma_done  : std_logic;
   signal rx_dma_tag   : std_logic_vector(15 downto 0);

   signal tx_dma_addr  : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal tx_dma_dout  : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal tx_dma_req   : std_logic;
   signal tx_dma_ack   : std_logic;
   signal tx_dma_done  : std_logic;
   signal tx_dma_tag   : std_logic_vector(15 downto 0);

   signal nf2f_data_out     : std_logic_vector(4*DMA_DATA_WIDTH-1 downto 0);
   signal nf2f_data_vld     : std_logic;
   signal nf2f_block_addr   : std_logic_vector(1 downto 0);
   signal nf2f_read         : std_logic;
   signal nf2f_empty        : std_logic_vector(3 downto 0);

   signal cnt_nf2f_addr     : std_logic_vector(1 downto 0);
   signal cnt_nf2f_addr_ce  : std_logic;

   signal data2bm_rx_src_rdy_n : std_logic;
   signal data2bm_rx_dst_rdy_n : std_logic;
   signal data2bm_dma_tag      : std_logic_vector(15 downto 0);
   signal data2bm_dma_done     : std_logic;

   signal ddm_src_rdy_n   : std_logic;
   signal ddm_data        : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal sum_src_rdy_n   : std_logic;
   signal sum_data        : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal rx_src_rdy_n   : std_logic;
   signal rx_data        : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal tx_src_rdy_n   : std_logic;
   signal tx_data        : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);

   signal nf2f_data_in    : std_logic_vector(127 downto 0);
   signal nf2f_write      : std_logic_vector(3 downto 0);
   signal nf2f_full       : std_logic_vector(3 downto 0);
   signal dec_dma_done     : std_logic_vector(3 downto 0);

   signal ddm_mi_sw_ardy   : std_logic;
   signal ddm_mi_sw_drdy   : std_logic;
   signal ddm_mi_sw_drd    : std_logic_vector(31 downto 0);
   signal sum_mi_sw_ardy   : std_logic;
   signal sum_mi_sw_drdy   : std_logic;
   signal sum_mi_sw_drd    : std_logic_vector(31 downto 0);
   signal mux_mi_drd       : std_logic_vector(31 downto 0);
   signal mux_mi_drd_sel   : std_logic;

   signal sgaddr     : std_logic_vector(63 downto 0);
   signal sladdr     : std_logic_vector(31 downto 0);
   signal slen       : std_logic_vector(11 downto 0);
   signal stag       : std_logic_vector(15 downto 0);
   signal stype      : std_logic_vector(1  downto 0);
   signal sreq       : std_logic;
   signal sack       : std_logic;
   signal soptag       : std_logic_vector(15 downto 0);
   signal sdone      : std_logic;

   signal sTX_NEWLEN_DV : std_logic_vector(IFCS-1 downto 0);
   signal sTX_NEWLEN    : std_logic_vector(IFCS*16-1 downto 0);

   signal sRX_NEWLEN_RDY : std_logic_vector(IFCS-1 downto 0);
   signal sRX_RELLEN : std_logic_vector(IFCS*16-1 downto 0);
   signal sRX_RELLEN_DV : std_logic_vector(IFCS-1 downto 0);

   signal sIB_WR_RDY    : std_logic;
   signal sMI_SW_ARDY   : std_logic;
   signal sMI_SW_DRDY   : std_logic;
   signal sMI_SW_DRD    : std_logic_vector(31 downto 0);

begin
   gen_run_i: for i in 0 to IFCS-1 generate
      rx_run(i) <= ddm_run(2*i);
      tx_run(i) <= ddm_run(2*i+1);
   end generate;

   gen_ctrl_idle_i: for i in 0 to IFCS-1 generate
      ctrl_idle(2*i)   <= rx_idle(i);
      ctrl_idle(2*i+1) <= tx_idle(i);
   end generate;

sum_flush <= not ddm_run;
ddm_idle <= ctrl_idle and sum_idle;

IB_WR_RDY   <= sIB_WR_RDY;
-- ------------------------------------------------------------------
-- DDM Instantion
-- ------------------------------------------------------------------
ddm_i: entity work.ddm
   generic map (
      BASE_ADDR         => DDM_IB_BASE,
      IFCS              => IFCS,
      BLOCK_SIZE        => BLOCK_SIZE,
      DMA_ID            => DDM_DMA_ID,
      DMA_DATA_WIDTH    => DMA_DATA_WIDTH,
      NFIFO_LUT_MEMORY  => false
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      -- status control
      RUN            => ddm_run,
      INIT           => ddm_init,
      IDLE           => ddm_idle,

      -- Data interface
      -- Write interface
      IB_WR_ADDR     => IB_WR_ADDR,
      IB_WR_DATA     => IB_WR_DATA,
      IB_WR_BE       => IB_WR_BE,
      IB_WR_REQ      => IB_WR_REQ,
      IB_WR_RDY      => sIB_WR_RDY,

      -- BM interface
      -- Memory interface
      DMA_ADDR        => ddm_dma_addr,
      DMA_DOUT        => ddm_dma_dout,
      DMA_REQ         => ddm_dma_req,
      DMA_ACK         => ddm_dma_ack,
      DMA_DONE        => ddm_dma_done,
      DMA_TAG         => ddm_dma_tag,
      DMA_IFC         => open, 

      -- SW memory interface
      MI_SW_DWR      => MI_SW_DWR,
      MI_SW_ADDR     => MI_SW_ADDR,
      MI_SW_RD       => MI_SW_RD,
      MI_SW_WR       => MI_SW_WR,
      MI_SW_BE       => MI_SW_BE,
      MI_SW_DRD      => ddm_mi_sw_drd,
      MI_SW_ARDY     => ddm_mi_sw_ardy,
      MI_SW_DRDY     => ddm_mi_sw_drdy,

      -- RxReqFifo interface
      RX_RF_ADDR     => ddm_rf_addr,
      RX_RF_DATA     => ddm_rf_data,
      RX_RF_DATA_VLD => ddm_rf_data_vld,
      RX_RF_FULL     => ddm_rf_full,
      RX_RF_INIT     => ddm_rf_init,

      -- Rx nfifo to rx_dma_ctrl
      RX_NFIFO_DOUT     => rx_nfifo_dout,
      RX_NFIFO_DOUT_VLD => rx_nfifo_dout_vld,
      RX_NFIFO_RADDR    => rx_nfifo_raddr,
      RX_NFIFO_RD       => rx_nfifo_rd,
      RX_NFIFO_EMPTY    => rx_nfifo_empty,
                                            
      -- Tx nfifo to tx_dma_ctrl
      TX_NFIFO_DOUT     => tx_nfifo_dout,
      TX_NFIFO_DOUT_VLD => tx_nfifo_dout_vld,
      TX_NFIFO_RADDR    => tx_nfifo_raddr,
      TX_NFIFO_RD       => tx_nfifo_rd,
      TX_NFIFO_EMPTY    => tx_nfifo_empty

   );

ddm_dma2data_i: entity work.DMA2DATA
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      DMA_ADDR       => ddm_dma_addr,
      DMA_DOUT       => ddm_dma_dout,
      DMA_REQ        => ddm_dma_req,
      DMA_ACK        => ddm_dma_ack,
      DMA_DONE       => ddm_dma_done,
      DMA_TAG        => ddm_dma_tag,

      -- output interface
      TX_SRC_RDY_N   => ddm_src_rdy_n,
      TX_DST_RDY_N   => nf2f_full(0),
      TX_DATA        => ddm_data,

      -- output tag interface
      TX_DMA_DONE    => dec_dma_done(0),
      TX_DMA_TAG     => data2bm_dma_tag
   );

sMI_SW_ARDY <= ddm_mi_sw_ardy or sum_mi_sw_ardy;
sMI_SW_DRDY <= ddm_mi_sw_drdy or sum_mi_sw_drdy;
sMI_SW_DRD  <= mux_mi_drd;
MI_SW_ARDY <= sMI_SW_ARDY;
MI_SW_DRDY <= sMI_SW_DRDY;
MI_SW_DRD  <= sMI_SW_DRD;

mux_mi_drd_sel <= ddm_mi_sw_drdy;
-- multiplexor mux_mi_drd ------------------------------------------------------
mux_mi_drdp: process(mux_mi_drd_sel, ddm_mi_sw_drd, sum_mi_sw_drd)
begin
   case mux_mi_drd_sel is
      when '0' => mux_mi_drd <= sum_mi_sw_drd;
      when '1' => mux_mi_drd <= ddm_mi_sw_drd;
      when others => mux_mi_drd <= (others => 'X');
   end case;
end process;

-- ------------------------------------------------------------------
-- Rx request fifo - connects ddm and sum
-- ------------------------------------------------------------------
rf_nfifo_i: entity work.nfifo
  generic map (
    DATA_WIDTH => log2(BLOCK_SIZE)+64+1,
    FLOWS      => IFCS,
    BLOCK_SIZE => RF_NFIFO_BLOCK_SIZE,
    LUT_MEMORY => RF_NFIFO_LUT_MEMORY,
    OUTPUT_REG => RF_NFIFO_OUTPUT_REG
  )
  port map (
    CLK         => CLK,
    RESET       => RESET,
    INIT        => ddm_rf_init,

    -- Write interface
    DATA_IN     => ddm_rf_data,
    WR_BLK_ADDR => ddm_rf_addr,
    WRITE       => ddm_rf_data_vld,
    FULL        => ddm_rf_full,

    -- Read interface
    DATA_OUT    => sum_rf_dout,
    DATA_VLD    => sum_rf_dvld,
    RD_BLK_ADDR => sum_rf_raddr,
    READ        => sum_rf_read,
    PIPE_EN     => sum_rf_read,
    EMPTY       => sum_rf_empty,

    STATUS      => sum_rf_status
  );

-- ------------------------------------------------------------------
-- SUM Instantion
-- ------------------------------------------------------------------
sum_i: entity work.sum
   generic map (
      BASE_ADDR         => SUM_IB_BASE,
      IFCS              => IFCS,
      BLOCK_SIZE        => BLOCK_SIZE,
      DMA_ID            => SUM_DMA_ID,
      DMA_DATA_WIDTH    => DMA_DATA_WIDTH,
      NFIFO_LUT_MEMORY  => false
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      INTERRUPT   => INTERRUPT,

      IDLE        => sum_idle,
      FLUSH       => sum_flush,
      INIT        => ddm_init,
      -- Data interface
      -- Read interface
      IB_RD_ADDR     => IB_RD_ADDR,
      IB_RD_DATA     => IB_RD_DATA,
      IB_RD_BE       => IB_RD_BE,
      IB_RD_REQ      => IB_RD_REQ,
      IB_RD_ARDY     => IB_RD_ARDY,
      IB_RD_SRC_RDY  => IB_RD_SRC_RDY,

      -- BM interface
      -- Memory interface
      DMA_ADDR        => sum_dma_addr,
      DMA_DOUT        => sum_dma_dout,
      DMA_REQ         => sum_dma_req,
      DMA_ACK         => sum_dma_ack,
      DMA_DONE        => sum_dma_done,
      DMA_TAG         => sum_dma_tag,

      -- SW memory interface
      MI_SW_DWR      => MI_SW_DWR,
      MI_SW_ADDR     => MI_SW_ADDR,
      MI_SW_RD       => MI_SW_RD,
      MI_SW_WR       => MI_SW_WR,
      MI_SW_BE       => MI_SW_BE,
      MI_SW_DRD      => sum_mi_sw_drd,
      MI_SW_ARDY     => sum_mi_sw_ardy,
      MI_SW_DRDY     => sum_mi_sw_drdy,

      -- RxReqFifo interface
      RX_RF_RADDR   => sum_rf_raddr,
      RX_RF_DOUT    => sum_rf_dout,
      RX_RF_DVLD    => sum_rf_dvld,
      RX_RF_EMPTY   => sum_rf_empty,
      RX_RF_READ    => sum_rf_read,
      RX_RF_STATUS  => sum_rf_status,

      -- Rx status update
      RX_SU_ADDR     => rx_su_addr,
      RX_SU_DATA     => rx_su_data,
      RX_SU_DVLD     => rx_su_dvld,
      RX_SU_HFULL    => rx_su_hfull,

      -- Tx status update
      TX_SU_ADDR     => tx_su_addr,
      TX_SU_DATA     => tx_su_data,
      TX_SU_DVLD     => tx_su_dvld,
      TX_SU_HFULL    => tx_su_hfull

   );

sum_dma2data_i: entity work.DMA2DATA
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      DMA_ADDR       => sum_dma_addr,
      DMA_DOUT       => sum_dma_dout,
      DMA_REQ        => sum_dma_req,
      DMA_ACK        => sum_dma_ack,
      DMA_DONE       => sum_dma_done,
      DMA_TAG        => sum_dma_tag,

      -- output interface
      TX_SRC_RDY_N   => sum_src_rdy_n,
      TX_DST_RDY_N   => nf2f_full(1),
      TX_DATA        => sum_data,

      -- output tag interface
      TX_DMA_DONE    => dec_dma_done(1),
      TX_DMA_TAG     => data2bm_dma_tag
   );

RX_NEWLEN_RDY <= sRX_NEWLEN_RDY;
RX_RELLEN     <= sRX_RELLEN;
RX_RELLEN_DV  <= sRX_RELLEN_DV;


-- ------------------------------------------------------------------
-- Rx ctrl Instantion
-- ------------------------------------------------------------------
rx_ctrl_i: entity work.rx_ctrl
   generic map (
      BUFFER_ADDR    => RX_BUFFER_ADDR,
      BUFFER_GAP     => RX_BUFFER_GAP,
      BUFFER_SIZE    => RX_BUFFER_SIZE,
      DMA_ID         => RX_DMA_ID,
      DMA_DATA_WIDTH => DMA_DATA_WIDTH,
      CHANNELS       => IFCS,
      BLOCK_SIZE     => BLOCK_SIZE
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      -- status control
      RUN            => rx_run,
      IDLE           => rx_idle,

      -- Receive buffer interface
      BUF_NEWLEN     => RX_NEWLEN,
      BUF_NEWLEN_DV  => RX_NEWLEN_DV,
      BUF_NEWLEN_RDY => sRX_NEWLEN_RDY,
      BUF_RELLEN     => sRX_RELLEN,
      BUF_RELLEN_DV  => sRX_RELLEN_DV,

      -- descriptors from ddm
      DESC_READ      => rx_nfifo_rd,
      DESC_ADDR      => rx_nfifo_raddr,
      DESC_DO        => rx_nfifo_dout,
      DESC_DO_VLD    => rx_nfifo_dout_vld,
      DESC_EMPTY     => rx_nfifo_empty,
 
      -- BM interface
      -- Memory interface
      DMA_ADDR       => rx_dma_addr,
      DMA_DOUT       => rx_dma_dout,
      DMA_REQ        => rx_dma_req,
      DMA_ACK        => rx_dma_ack,
      DMA_DONE       => rx_dma_done,
      DMA_TAG        => rx_dma_tag,

      -- status update
      SU_ADDR        => rx_su_addr,
      SU_DATA        => rx_su_data,
      SU_DATA_VLD    => rx_su_dvld,
      SU_HFULL       => rx_su_hfull

   );

rx_dma2data_i: entity work.DMA2DATA
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      DMA_ADDR       => rx_dma_addr,
      DMA_DOUT       => rx_dma_dout,
      DMA_REQ        => rx_dma_req,
      DMA_ACK        => rx_dma_ack,
      DMA_DONE       => rx_dma_done,
      DMA_TAG        => rx_dma_tag,

      -- output interface
      TX_SRC_RDY_N   => rx_src_rdy_n,
      TX_DST_RDY_N   => nf2f_full(2),
      TX_DATA        => rx_data,

      -- output tag interface
      TX_DMA_DONE    => dec_dma_done(2),
      TX_DMA_TAG     => data2bm_dma_tag
   );

   TX_NEWLEN_DV  <= sTX_NEWLEN_DV;
   TX_NEWLEN     <= sTX_NEWLEN;
-- ------------------------------------------------------------------
-- Tx Ctrl
-- ------------------------------------------------------------------
tx_ctrl_i: entity work.tx_ctrl
   generic map (
      BUFFER_ADDR    => TX_BUFFER_ADDR,
      BUFFER_GAP     => TX_BUFFER_GAP,
      BUFFER_SIZE    => TX_BUFFER_SIZE,
      DMA_ID         => TX_DMA_ID,
      DMA_DATA_WIDTH => DMA_DATA_WIDTH,
      CHANNELS       => IFCS,
      BLOCK_SIZE     => BLOCK_SIZE
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      -- status control
      RUN            => tx_run,
      IDLE           => tx_idle,

      -- Receive buffer interface
      BUF_NEWLEN     => sTX_NEWLEN,
      BUF_NEWLEN_DV  => sTX_NEWLEN_DV,
      BUF_NEWLEN_RDY => TX_NEWLEN_RDY,
      BUF_RELLEN     => TX_RELLEN,
      BUF_RELLEN_DV  => TX_RELLEN_DV,

      -- descriptors from ddm
      DESC_READ      => tx_nfifo_rd,
      DESC_ADDR      => tx_nfifo_raddr,
      DESC_DO        => tx_nfifo_dout,
      DESC_DO_VLD    => tx_nfifo_dout_vld,
      DESC_EMPTY     => tx_nfifo_empty,
 
       -- BM interface
      -- Memory interface
      DMA_ADDR       => tx_dma_addr,
      DMA_DOUT       => tx_dma_dout,
      DMA_REQ        => tx_dma_req,
      DMA_ACK        => tx_dma_ack,
      DMA_DONE       => tx_dma_done,
      DMA_TAG        => tx_dma_tag,

      -- status update
      SU_ADDR        => tx_su_addr,
      SU_DATA        => tx_su_data,
      SU_DATA_VLD    => tx_su_dvld,
      SU_HFULL       => tx_su_hfull

   );

tx_dma2data_i: entity work.DMA2DATA
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- input interface
      DMA_ADDR       => tx_dma_addr,
      DMA_DOUT       => tx_dma_dout,
      DMA_REQ        => tx_dma_req,
      DMA_ACK        => tx_dma_ack,
      DMA_DONE       => tx_dma_done,
      DMA_TAG        => tx_dma_tag,

      -- output interface
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => nf2f_full(3),
      TX_DATA        => tx_data,

      -- output tag interface
      TX_DMA_DONE    => dec_dma_done(3),
      TX_DMA_TAG     => data2bm_dma_tag
   );

-- ------------------------------------------------------------------
-- nf2f connection to bm interface
-- ------------------------------------------------------------------
nf2f_data_in <= tx_data  & rx_data & 
                sum_data & ddm_data;

nf2f_write   <= (not tx_src_rdy_n)  & (not rx_src_rdy_n) & 
                (not sum_src_rdy_n) & (not ddm_src_rdy_n);

-- multififo for bm requests
bm_nf2f_i: entity work.NFIFO2FIFO
   generic map(
      DATA_WIDTH  => 4*DMA_DATA_WIDTH,
      FLOWS       => 4,
      BLOCK_SIZE  => 2,
      LUT_MEMORY  => true,
      GLOB_STATE  => false,
      OUTPUT_REG  => false
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      
      -- write interface
      DATA_IN     => nf2f_data_in,
      WRITE       => nf2f_write,
      FULL        => nf2f_full,

      -- read innterface
      DATA_OUT    => nf2f_data_out,
      DATA_VLD    => nf2f_data_vld,
      BLOCK_ADDR  => nf2f_block_addr,
      READ        => nf2f_read,
      PIPE_EN     => nf2f_read,
      EMPTY       => nf2f_empty
   );

   data2bm_rx_src_rdy_n <= not (nf2f_data_vld);
   nf2f_read            <= not data2bm_rx_dst_rdy_n;

-- convert dma request in simple format to BM
data2bm_i: entity work.DATA2BM
   port map(
      CLK            => CLK,
      RESET          => RESET,
      -- input interface
      RX_SRC_RDY_N   => data2bm_rx_src_rdy_n,
      RX_DST_RDY_N   => data2bm_rx_dst_rdy_n,
      RX_DATA        => nf2f_data_out,
      -- input TAG interface
      RX_DMA_TAG     => data2bm_dma_tag,
      RX_DMA_DONE    => data2bm_dma_done,

      -- Bus master interface
      BM_GLOBAL_ADDR => sgaddr,
      BM_LOCAL_ADDR  => sladdr,
      BM_LENGTH      => slen,
      BM_TAG         => stag,
      BM_TRANS_TYPE  => stype,
      BM_REQ         => sreq,
      BM_ACK         => sack,
      -- Output               
      BM_OP_TAG      => soptag,
      BM_OP_DONE     => sdone
   );

IB_BM_GADDR  <= sgaddr;
IB_BM_LADDR  <= sladdr;
IB_BM_LENGTH <= slen;
IB_BM_TAG    <= stag;
IB_BM_TTYPE  <= stype;
IB_BM_REQ    <= sreq;
sack <= IB_BM_ACK;

soptag <= IB_BM_OP_TAG ;
sdone  <= IB_BM_OP_DONE;

nf2f_block_addr  <= cnt_nf2f_addr;
cnt_nf2f_addr_ce <= '1';

-- cnt_nf2f_addr counter
cnt_nf2f_addrp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (RESET = '1') then
         cnt_nf2f_addr <= (others => '0');
      elsif (cnt_nf2f_addr_ce = '1') then
         cnt_nf2f_addr <= cnt_nf2f_addr + 1;
      end if;
   end if;
end process;

dec1fn_dma_done_i: entity work.dec1fn_enable
   generic map (
      ITEMS    => 4
      )
   port map (
      ADDR     => data2bm_dma_tag(1 downto 0),
      ENABLE   => data2bm_dma_done,
      DO       => dec_dma_done
   );

      -- -------------------------------------------------------------------------
      --                             CHIPSCOPE
      -- -------------------------------------------------------------------------
CHIPSCOPE_I: if (false) generate begin
   ICON3_I : icon3
   port map(
              CONTROL0 => control0,
              CONTROL1 => control1,
              CONTROL2 => control2
           );

   ila144_trig0 <= "000"                   --  3
                   & sgaddr                -- 64
                   & sladdr                -- 32
                   & slen                  -- 12
                   & stag(11 downto 0)     -- 12
                   & stype                 --  2 
                   & sreq                  --  1 
                   & sack                  --  1 
                   & soptag                -- 16
                   & sdone;                --  1
                                           --===
                                           --144

   ILA144_I0 : ila144
   port map(
              CONTROL => control0,
              CLK     => CLK,
              TRIG0   => ila144_trig0
           );

--    ila144_trig1 <= "0"                         --  1
--                    & tx_nfifo_empty            --  2
--                    & tx_nfifo_dout_vld         --  1
--                    & tx_nfifo_dout             -- 64
--                    & tx_nfifo_raddr            --  1
--                    & tx_nfifo_rd               --  1
--                    & TX_RELLEN_DV              --  2
--                    & TX_RELLEN                 -- 32
--                    & TX_NEWLEN_RDY             --  2
--                    & sTX_NEWLEN_DV             --  2
--                    & sTX_NEWLEN                -- 32
--                    & tx_idle                   --  2
--                    & tx_run;                   --  2
--                                                --===
--                                                --144

   ila144_trig1 <=  "0000" & "0000" & "0000" & "0000"
                  & "0000" & "0000" & "0000" & "0000"
                  & "0000" & "0000"    -- 40
                      & MI_SW_DWR      -- 32
                      & MI_SW_ADDR     -- 32
                      & MI_SW_RD       --  1
                      & MI_SW_WR       --  1
                      & MI_SW_BE       --  4
                      & sMI_SW_DRD     -- 32
                      & sMI_SW_ARDY    --  1
                      & sMI_SW_DRDY;   --  1

   ILA144_I1 : ila144
   port map(
              CONTROL => control1,
              CLK     => CLK,
              TRIG0   => ila144_trig1
           );

--    ila144_trig2 <= "0"                         --  1
--                    & rx_nfifo_empty            --  2
--                    & rx_nfifo_dout_vld         --  1
--                    & rx_nfifo_dout             -- 64
--                    & rx_nfifo_raddr            --  1
--                    & rx_nfifo_rd               --  1
--                    & sRX_RELLEN_DV              --  2
--                    & sRX_RELLEN                 -- 32
--                    & sRX_NEWLEN_RDY             --  2
--                    & RX_NEWLEN_DV              --  2
--                    & RX_NEWLEN                 -- 32
--                    & rx_idle                   --  2
--                    & rx_run;                   --  2
--                                                --===
--                                                --144

    ila144_trig2 <= "0000" & "0000" & "0000" & "0000"
                  & "0000" & "0000" & "0000" & "0000"
                  & "0000" & "00"         -- 38
                    & IB_WR_ADDR          -- 32
                    & IB_WR_DATA          -- 64
                    & IB_WR_BE            --  8
                    & IB_WR_REQ           --  1
                    & sIB_WR_RDY;         --  1


   ILA144_I2 : ila144
   port map(
              CONTROL => control2,
              CLK     => CLK,
              TRIG0   => ila144_trig2
           );

end generate;
-- -------------------------------------------------------------------------
--                             END OF DEBUG
-- -------------------------------------------------------------------------
end architecture pac_behav;
