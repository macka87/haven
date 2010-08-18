--*****************************************************************************
-- DISCLAIMER OF LIABILITY
--
-- This file contains proprietary and confidential information of
-- Xilinx, Inc. ("Xilinx"), that is distributed under a license
-- from Xilinx, and may be used, copied and/or disclosed only
-- pursuant to the terms of a valid license agreement with Xilinx.
--
-- XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION
-- ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER
-- EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT
-- LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,
-- MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx
-- does not warrant that functions included in the Materials will
-- meet the requirements of Licensee, or that the operation of the
-- Materials will be uninterrupted or error-free, or that defects
-- in the Materials will be corrected. Furthermore, Xilinx does
-- not warrant or make any representations regarding use, or the
-- results of the use, of the Materials in terms of correctness,
-- accuracy, reliability or otherwise.
--
-- Xilinx products are not designed or intended to be fail-safe,
-- or for use in any application requiring fail-safe performance,
-- such as life-support or safety devices or systems, Class III
-- medical devices, nuclear facilities, applications related to
-- the deployment of airbags, or any other applications that could
-- lead to death, personal injury or severe property or
-- environmental damage (individually and collectively, "critical
-- applications"). Customer assumes the sole risk and liability
-- of any use of Xilinx products in critical applications,
-- subject only to applicable laws and regulations governing
-- limitations on product liability.
--
-- Copyright 2006, 2007, 2008 Xilinx, Inc.
-- All rights reserved.
--
-- This disclaimer and copyright notice must be retained as part
-- of this file at all times.
--*****************************************************************************
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor             : Xilinx
-- \   \   \/     Version            : 3.3
--  \   \         Application        : MIG
--  /   /         Filename           : qdrii_top.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Serves as the top level memory interface module that interfaces to
--      the user backend.
--       2. Instantiates the user interface module, the controller statemachine
--      and the phy layer.
--
--Revision History:
--   Rev 1.1 - Parameter IODELAY_GRP added. PK. 11/27/08
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_top is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    ADDR_WIDTH            : integer := 19;
    BURST_LENGTH          : integer := 4;
    BW_WIDTH              : integer := 8;
    CLK_PERIOD            : integer := 3333;
    CLK_WIDTH             : integer := 2;
    CQ_WIDTH              : integer := 2;
    DATA_WIDTH            : integer := 72;
    DEBUG_EN              : integer := 0;
    HIGH_PERFORMANCE_MODE : boolean := TRUE;
    IODELAY_GRP           : string  := "IODELAY_MIG";
    MEMORY_WIDTH          : integer := 36;
    SIM_ONLY              : integer := 0
    );
  port(
    clk0                                 : in  std_logic;
    clk180                               : in  std_logic;
    clk270                               : in  std_logic;
    user_rst_0                           : in  std_logic;
    user_rst_180                         : in  std_logic;
    user_rst_270                         : in  std_logic;
    user_ad_w_n                          : in  std_logic;
    user_d_w_n                           : in  std_logic;
    user_ad_wr                           : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    user_bwh_n                           : in  std_logic_vector(BW_WIDTH-1 downto 0);
    user_bwl_n                           : in  std_logic_vector(BW_WIDTH-1 downto 0);
    user_dwl                             : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_dwh                             : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_r_n                             : in  std_logic;
    user_ad_rd                           : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    idelay_ctrl_rdy                      : in  std_logic;
    qdr_q                                : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    qdr_cq                               : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    qdr_cq_n                             : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    user_wr_full                         : out std_logic;
    user_rd_full                         : out std_logic;
    user_qrl                             : out std_logic_vector(DATA_WIDTH-1 downto 0);
    user_qrh                             : out std_logic_vector(DATA_WIDTH-1 downto 0);
    user_qr_valid                        : out std_logic;
    cal_done                             : out std_logic;
    qdr_c                                : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_c_n                              : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_dll_off_n                        : out std_logic;
    qdr_k                                : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_k_n                              : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_sa                               : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    qdr_bw_n                             : out std_logic_vector(BW_WIDTH-1 downto 0);
    qdr_w_n                              : out std_logic;
    qdr_d                                : out std_logic_vector(DATA_WIDTH-1 downto 0);
    qdr_r_n                              : out std_logic;
    -- Debug Signals
    dbg_idel_up_all                      : in  std_logic;
    dbg_idel_down_all                    : in  std_logic;
    dbg_idel_up_q_cq                     : in  std_logic;
    dbg_idel_down_q_cq                   : in  std_logic;
    dbg_idel_up_q_cq_n                   : in  std_logic;
    dbg_idel_down_q_cq_n                 : in  std_logic;
    dbg_idel_up_cq                       : in  std_logic;
    dbg_idel_down_cq                     : in  std_logic;
    dbg_idel_up_cq_n                     : in  std_logic;
    dbg_idel_down_cq_n                   : in  std_logic;
    dbg_sel_idel_q_cq                    : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_sel_all_idel_q_cq                : in  std_logic;
    dbg_sel_idel_q_cq_n                  : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_sel_all_idel_q_cq_n              : in  std_logic;
    dbg_sel_idel_cq                      : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_sel_all_idel_cq                  : in  std_logic;
    dbg_sel_idel_cq_n                    : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_sel_all_idel_cq_n                : in  std_logic;
    dbg_init_count_done                  : out std_logic;
    dbg_q_cq_init_delay_done             : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_q_cq_n_init_delay_done           : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_q_cq_init_delay_done_tap_count   : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
    dbg_q_cq_n_init_delay_done_tap_count : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
    dbg_cq_cal_done                      : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_cq_n_cal_done                    : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_cq_cal_tap_count                 : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
    dbg_cq_n_cal_tap_count               : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
    dbg_we_cal_done_cq                   : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_we_cal_done_cq_n                 : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_cq_q_data_valid                  : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_cq_n_q_data_valid                : out std_logic_vector(CQ_WIDTH-1 downto 0);
    dbg_cal_done                         : out std_logic;
    dbg_data_valid                       : out std_logic
    );
end entity qdrii_top;

architecture arch_qdrii_top of qdrii_top is

  constant Q_PER_CQ : integer := DATA_WIDTH/((CQ_WIDTH*(MEMORY_WIDTH/36))+CQ_WIDTH);
  -- Number of read data bits associated with a single read strobe. For a 36 bit
  -- component the value is always 18 because it is defined as number of
  -- read data bits associated with CQ and CQ#. For 18 bit components the value
  -- is always DATA_WIDTH/CQ_WIDTH, because it is defined as number of read data
  -- bits associated with CQ.

  signal wr_init_n     : std_logic;
  signal rd_init_n     : std_logic;
  signal wr_init2_n    : std_logic;
  signal fifo_ad_wr    : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_rd    : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_bw_h     : std_logic_vector(BW_WIDTH-1 downto 0);
  signal fifo_bw_l     : std_logic_vector(BW_WIDTH-1 downto 0);
  signal fifo_dwl      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal fifo_dwh      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal fifo_wr_empty : std_logic;
  signal fifo_rd_empty : std_logic;
  signal fifo_qr_full  : std_logic;
  signal rd_qrl        : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal rd_qrh        : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal data_valid    : std_logic;
  signal rd_data_valid : std_logic;
  signal cal_done_i    : std_logic;
  signal cal_done_r    : std_logic;
  signal dummy_wrl     : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dummy_wrh     : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dummy_wren    : std_logic;

  component qdrii_top_ctrl_sm
    generic(
      BURST_LENGTH : integer := BURST_LENGTH
      );
    port(
      clk0        : in std_logic;
      user_rst_0  : in std_logic;
      wr_empty    : in std_logic;
      rd_empty    : in std_logic;
      cal_done    : in std_logic;
      wr_init_n   : out std_logic;
      rd_init_n   : out std_logic
      );
  end component qdrii_top_ctrl_sm;

  component qdrii_top_user_interface
    generic(
      ADDR_WIDTH   : integer := ADDR_WIDTH;
      BURST_LENGTH : integer := BURST_LENGTH;
      BW_WIDTH     : integer := BW_WIDTH;
      DATA_WIDTH   : integer := DATA_WIDTH
      );
    port(
      clk0          : in std_logic;
      user_rst_0    : in std_logic;
      clk270        : in std_logic;
      user_rst_270  : in std_logic;
      cal_done      : in std_logic;
      user_ad_w_n   : in std_logic;
      user_d_w_n    : in std_logic;
      user_ad_wr    : in std_logic_vector(ADDR_WIDTH-1 downto 0);
      user_bw_h     : in std_logic_vector(BW_WIDTH-1 downto 0);
      user_bw_l     : in std_logic_vector(BW_WIDTH-1 downto 0);
      user_dwl      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      user_dwh      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      wr_init_n     : in std_logic;
      wr_init2_n    : in std_logic;
      user_r_n      : in std_logic;
      user_ad_rd    : in std_logic_vector(ADDR_WIDTH-1 downto 0);
      rd_init_n     : in std_logic;
      dummy_wrl     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      dummy_wrh     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      dummy_wren    : in std_logic;
      user_wr_full  : out std_logic;
      fifo_ad_wr    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      fifo_bw_h     : out std_logic_vector(BW_WIDTH-1 downto 0);
      fifo_bw_l     : out std_logic_vector(BW_WIDTH-1 downto 0);
      fifo_dwl      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      fifo_dwh      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      fifo_wr_empty : out std_logic;
      user_rd_full  : out std_logic;
      fifo_ad_rd    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      fifo_rd_empty : out std_logic
      );
  end component qdrii_top_user_interface;

  component qdrii_top_phy
     generic (
       ADDR_WIDTH            : integer := ADDR_WIDTH;
       BURST_LENGTH          : integer := BURST_LENGTH;
       BW_WIDTH              : integer := BW_WIDTH;
       CLK_PERIOD            : integer := CLK_PERIOD;
       CLK_WIDTH             : integer := CLK_WIDTH;
       CQ_WIDTH              : integer := CQ_WIDTH;
       DATA_WIDTH            : integer := DATA_WIDTH;
       DEBUG_EN              : integer := DEBUG_EN;
       HIGH_PERFORMANCE_MODE : boolean := HIGH_PERFORMANCE_MODE;
       IODELAY_GRP           : string  := IODELAY_GRP;
       MEMORY_WIDTH          : integer := MEMORY_WIDTH;
       Q_PER_CQ              : integer := Q_PER_CQ;
       SIM_ONLY              : integer := SIM_ONLY
       );
     port (
       clk0                                 : in std_logic;
       clk180                               : in std_logic;
       clk270                               : in std_logic;
       user_rst_0                           : in std_logic;
       user_rst_180                         : in std_logic;
       user_rst_270                         : in std_logic;
       wr_init_n                            : in std_logic;
       rd_init_n                            : in std_logic;
       fifo_ad_wr                           : in std_logic_vector(ADDR_WIDTH-1 downto 0);
       fifo_bw_h                            : in std_logic_vector(BW_WIDTH-1 downto 0);
       fifo_bw_l                            : in std_logic_vector(BW_WIDTH-1 downto 0);
       fifo_dwl                             : in std_logic_vector(DATA_WIDTH-1 downto 0);
       fifo_dwh                             : in std_logic_vector(DATA_WIDTH-1 downto 0);
       fifo_ad_rd                           : in std_logic_vector(ADDR_WIDTH-1 downto 0);
       idelay_ctrl_rdy                      : in std_logic;
       qdr_q                                : in std_logic_vector(DATA_WIDTH-1 downto 0);
       qdr_cq                               : in std_logic_vector(CQ_WIDTH-1 downto 0);
       qdr_cq_n                             : in std_logic_vector(CQ_WIDTH-1 downto 0);
       rd_qrl                               : out std_logic_vector(DATA_WIDTH-1 downto 0);
       rd_qrh                               : out std_logic_vector(DATA_WIDTH-1 downto 0);
       data_valid                           : out std_logic;
       cal_done                             : out std_logic;
       wr_init2_n                           : out std_logic;
       --Indicates that the calibration of Input delay tap is done
       qdr_c                                : out std_logic_vector(CLK_WIDTH-1 downto 0);
       qdr_c_n                              : out std_logic_vector(CLK_WIDTH-1 downto 0);
       qdr_dll_off_n                        : out std_logic;
       qdr_k                                : out std_logic_vector(CLK_WIDTH-1 downto 0);
       qdr_k_n                              : out std_logic_vector(CLK_WIDTH-1 downto 0);
       qdr_sa                               : out std_logic_vector(ADDR_WIDTH-1 downto 0);
       qdr_bw_n                             : out std_logic_vector(BW_WIDTH-1 downto 0);
       qdr_w_n                              : out std_logic;
       qdr_d                                : out std_logic_vector(DATA_WIDTH-1 downto 0);
       qdr_r_n                              : out std_logic;
       dummy_wrl                            : out std_logic_vector(DATA_WIDTH-1 downto 0);
       dummy_wrh                            : out std_logic_vector(DATA_WIDTH-1 downto 0);
       dummy_wren                           : out std_logic;
       -- Debug Signals
       dbg_idel_up_all                      : in  std_logic;
       dbg_idel_down_all                    : in  std_logic;
       dbg_idel_up_q_cq                     : in  std_logic;
       dbg_idel_down_q_cq                   : in  std_logic;
       dbg_idel_up_q_cq_n                   : in  std_logic;
       dbg_idel_down_q_cq_n                 : in  std_logic;
       dbg_idel_up_cq                       : in  std_logic;
       dbg_idel_down_cq                     : in  std_logic;
       dbg_idel_up_cq_n                     : in  std_logic;
       dbg_idel_down_cq_n                   : in  std_logic;
       dbg_sel_idel_q_cq                    : in  std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_sel_all_idel_q_cq                : in  std_logic;
       dbg_sel_idel_q_cq_n                  : in  std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_sel_all_idel_q_cq_n              : in  std_logic;
       dbg_sel_idel_cq                      : in  std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_sel_all_idel_cq                  : in  std_logic;
       dbg_sel_idel_cq_n                    : in  std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_sel_all_idel_cq_n                : in  std_logic;
       dbg_init_count_done                  : out std_logic;
       dbg_q_cq_init_delay_done             : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_q_cq_n_init_delay_done           : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_q_cq_init_delay_done_tap_count   : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
       dbg_q_cq_n_init_delay_done_tap_count : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
       dbg_cq_cal_done                      : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_cq_n_cal_done                    : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_cq_cal_tap_count                 : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
       dbg_cq_n_cal_tap_count               : out std_logic_vector((6*CQ_WIDTH)-1 downto 0);
       dbg_we_cal_done_cq                   : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_we_cal_done_cq_n                 : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_cq_q_data_valid                  : out std_logic_vector(CQ_WIDTH-1 downto 0);
       dbg_cq_n_q_data_valid                : out std_logic_vector(CQ_WIDTH-1 downto 0)
       );
  end component qdrii_top_phy;

begin

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      dbg_cal_done  <= cal_done_i;
    end if;
  end process;

  dbg_data_valid <= data_valid when (cal_done_r = '1') else '0';

  user_qrl      <= rd_qrl;
  user_qrh      <= rd_qrh;
  user_qr_valid <= data_valid when (cal_done_r = '1') else '0';
  cal_done      <= cal_done_i;

  CAL_DONE_FF : FDRSE
    generic map (
      INIT => '0'
      )
    port map (
      Q  => cal_done_r,
      C  => clk0,
      CE => '1',
      D  => cal_done_i,
      R  => '0',
      S  => '0'
      );

  U_QDRII_TOP_USER_INTERFACE : qdrii_top_user_interface
    generic map(
      ADDR_WIDTH   => ADDR_WIDTH,
      BURST_LENGTH => BURST_LENGTH,
      BW_WIDTH     => BW_WIDTH,
      DATA_WIDTH   => DATA_WIDTH
      )
    port map(
      clk0          => clk0,
      user_rst_0    => user_rst_0,
      clk270        => clk270,
      user_rst_270  => user_rst_270,
      cal_done      => cal_done_r,
      user_ad_w_n   => user_ad_w_n,
      user_d_w_n    => user_d_w_n,
      user_ad_wr    => user_ad_wr,
      user_bw_h     => user_bwh_n,
      user_bw_l     => user_bwl_n,
      user_dwl      => user_dwl,
      user_dwh      => user_dwh,
      wr_init_n     => wr_init_n,
      wr_init2_n    => wr_init2_n,
      user_r_n      => user_r_n,
      user_ad_rd    => user_ad_rd,
      rd_init_n     => rd_init_n,
      dummy_wrl     => dummy_wrl,
      dummy_wrh     => dummy_wrh,
      dummy_wren    => dummy_wren,
      user_wr_full  => user_wr_full,
      fifo_ad_wr    => fifo_ad_wr,
      fifo_bw_h     => fifo_bw_h,
      fifo_bw_l     => fifo_bw_l,
      fifo_dwl      => fifo_dwl,
      fifo_dwh      => fifo_dwh,
      fifo_wr_empty => fifo_wr_empty,
      user_rd_full  => user_rd_full,
      fifo_ad_rd    => fifo_ad_rd,
      fifo_rd_empty => fifo_rd_empty
      );

  U_QDRII_TOP_CTRL_SM : qdrii_top_ctrl_sm
    generic map(
      BURST_LENGTH => BURST_LENGTH
      )
    port map(
      clk0       => clk0,
      user_rst_0 => user_rst_0,
      wr_empty   => fifo_wr_empty,
      rd_empty   => fifo_rd_empty,
      cal_done   => cal_done_i,
      wr_init_n  => wr_init_n,
      rd_init_n  => rd_init_n
      );

  U_QDRII_TOP_PHY : qdrii_top_phy
    generic map(
      ADDR_WIDTH            => ADDR_WIDTH,
      BURST_LENGTH          => BURST_LENGTH,
      BW_WIDTH              => BW_WIDTH,
      CLK_PERIOD            => CLK_PERIOD,
      CLK_WIDTH             => CLK_WIDTH,
      CQ_WIDTH              => CQ_WIDTH,
      DATA_WIDTH            => DATA_WIDTH,
      DEBUG_EN              => DEBUG_EN,
      HIGH_PERFORMANCE_MODE => HIGH_PERFORMANCE_MODE,
      IODELAY_GRP           => IODELAY_GRP,
      MEMORY_WIDTH          => MEMORY_WIDTH,
      Q_PER_CQ              => Q_PER_CQ,
      SIM_ONLY              => SIM_ONLY
      )
    port map(
      clk0                                 => clk0,
      clk180                               => clk180,
      clk270                               => clk270,
      user_rst_0                           => user_rst_0,
      user_rst_180                         => user_rst_180,
      user_rst_270                         => user_rst_270,
      cal_done                             => cal_done_i,
      wr_init_n                            => wr_init_n,
      rd_init_n                            => rd_init_n,
      fifo_ad_wr                           => fifo_ad_wr,
      fifo_ad_rd                           => fifo_ad_rd,
      fifo_bw_h                            => fifo_bw_h,
      fifo_bw_l                            => fifo_bw_l,
      fifo_dwl                             => fifo_dwl,
      fifo_dwh                             => fifo_dwh,
      idelay_ctrl_rdy                      => idelay_ctrl_rdy,
      rd_qrl                               => rd_qrl,
      rd_qrh                               => rd_qrh,
      data_valid                           => data_valid,
      wr_init2_n                           => wr_init2_n,
      qdr_c                                => qdr_c,
      qdr_c_n                              => qdr_c_n,
      qdr_dll_off_n                        => qdr_dll_off_n,
      qdr_k                                => qdr_k,
      qdr_k_n                              => qdr_k_n,
      qdr_sa                               => qdr_sa,
      qdr_bw_n                             => qdr_bw_n,
      qdr_w_n                              => qdr_w_n,
      qdr_d                                => qdr_d,
      qdr_r_n                              => qdr_r_n,
      qdr_q                                => qdr_q,
      qdr_cq                               => qdr_cq,
      qdr_cq_n                             => qdr_cq_n,
      dummy_wrl                            => dummy_wrl,
      dummy_wrh                            => dummy_wrh,
      dummy_wren                           => dummy_wren,
      --Debug Signals
      dbg_idel_up_all                      => dbg_idel_up_all,
      dbg_idel_down_all                    => dbg_idel_down_all,
      dbg_idel_up_q_cq                     => dbg_idel_up_q_cq,
      dbg_idel_down_q_cq                   => dbg_idel_down_q_cq,
      dbg_idel_up_q_cq_n                   => dbg_idel_up_q_cq_n,
      dbg_idel_down_q_cq_n                 => dbg_idel_down_q_cq_n,
      dbg_idel_up_cq                       => dbg_idel_up_cq,
      dbg_idel_down_cq                     => dbg_idel_down_cq,
      dbg_idel_up_cq_n                     => dbg_idel_up_cq_n,
      dbg_idel_down_cq_n                   => dbg_idel_down_cq_n,
      dbg_sel_idel_q_cq                    => dbg_sel_idel_q_cq,
      dbg_sel_all_idel_q_cq                => dbg_sel_all_idel_q_cq,
      dbg_sel_idel_q_cq_n                  => dbg_sel_idel_q_cq_n,
      dbg_sel_all_idel_q_cq_n              => dbg_sel_all_idel_q_cq_n,
      dbg_sel_idel_cq                      => dbg_sel_idel_cq,
      dbg_sel_all_idel_cq                  => dbg_sel_all_idel_cq,
      dbg_sel_idel_cq_n                    => dbg_sel_idel_cq_n,
      dbg_sel_all_idel_cq_n                => dbg_sel_all_idel_cq_n,
      dbg_init_count_done                  => dbg_init_count_done,
      dbg_q_cq_init_delay_done             => dbg_q_cq_init_delay_done,
      dbg_q_cq_n_init_delay_done           => dbg_q_cq_n_init_delay_done,
      dbg_q_cq_init_delay_done_tap_count   => dbg_q_cq_init_delay_done_tap_count,
      dbg_q_cq_n_init_delay_done_tap_count => dbg_q_cq_n_init_delay_done_tap_count,
      dbg_cq_cal_done                      => dbg_cq_cal_done,
      dbg_cq_n_cal_done                    => dbg_cq_n_cal_done,
      dbg_cq_cal_tap_count                 => dbg_cq_cal_tap_count,
      dbg_cq_n_cal_tap_count               => dbg_cq_n_cal_tap_count,
      dbg_we_cal_done_cq                   => dbg_we_cal_done_cq,
      dbg_we_cal_done_cq_n                 => dbg_we_cal_done_cq_n,
      dbg_cq_q_data_valid                  => dbg_cq_q_data_valid,
      dbg_cq_n_q_data_valid                => dbg_cq_n_q_data_valid
      );

end architecture arch_qdrii_top;