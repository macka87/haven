--*****************************************************************************
-- DISCLAIMER OF LIABILITY
--
-- This text/file contains proprietary, confidential
-- information of Xilinx, Inc., is distributed under license
-- from Xilinx, Inc., and may be used, copied and/or
-- disclosed only pursuant to the terms of a valid license
-- agreement with Xilinx, Inc. Xilinx hereby grants you a
-- license to use this text/file solely for design, simulation,
-- implementation and creation of design files limited
-- to Xilinx devices or technologies. Use with non-Xilinx
-- devices or technologies is expressly prohibited and
-- immediately terminates your license unless covered by
-- a separate agreement.
--
-- Xilinx is providing this design, code, or information
-- "as-is" solely for use in developing programs and
-- solutions for Xilinx devices, with no obligation on the
-- part of Xilinx to provide support. By providing this design,
-- code, or information as one possible implementation of
-- this feature, application or standard, Xilinx is making no
-- representation that this implementation is free from any
-- claims of infringement. You are responsible for
-- obtaining any rights you may require for your implementation.
-- Xilinx expressly disclaims any warranty whatsoever with
-- respect to the adequacy of the implementation, including
-- but not limited to any warranties or representations that this
-- implementation is free from claims of infringement, implied
-- warranties of merchantability or fitness for a particular
-- purpose.
--
-- Xilinx products are not intended for use in life support
-- appliances, devices, or systems. Use in such applications is
-- expressly prohibited.
--
-- Any modifications that are made to the Source Code are
-- done at the user's sole risk and will be unsupported.
--
-- Copyright (c) 2006-2007 Xilinx, Inc. All rights reserved.
--
-- This copyright and support notice must be retained as part
-- of this text at all times.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor             : Xilinx
-- \   \   \/     Version            : 2.2
--  \   \         Application        : MIG
--  /   /         Filename           : qdrii_sram.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--   Top-level module. Simple model for what the user might use
--   typically, the user will only instantiate MEM_INTERFACE_TOP in their
--   code, and generate all the other infrastructure logic separately.
--   This module serves both as an example, and allows the user
--   to synthesize a self-contained design, which they can use to test their
--   hardware.
--   In addition to the memory controller, the module instantiates:
--     1. Reset logic based on user clocks
--     2. IDELAY control block
--     3. Synthesizable testbench - used to model user's backend logic
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;
use work.qdrii_chipscope.all;

entity qdrii_sram is
  generic(
   C0_QDRII_ADDR_WIDTH  : integer := 20; -- # of memory component addr bits
   C0_QDRII_BURST_LENGTH  : integer := 4; -- Burst Length type of memory component
   C0_QDRII_BW_WIDTH    : integer := 2; -- # of Byte Write Control bits
   QDRII_CLK_FREQ       : integer := 250; -- Core/Memory clock frequency (in MHz)
   C0_QDRII_CLK_WIDTH   : integer := 1; -- # of clock outputs
   C0_QDRII_CQ_WIDTH    : integer := 1; -- # of (CQ + CQ#) bits for x36 component; # of CQ bits for others
   C0_QDRII_DATA_WIDTH  : integer := 18; -- Design Data Width
   C0_QDRII_DEBUG_EN    : integer := 0; -- Enable debug signals/controls. When this parameter is changed from 0 to 1,
   -- make sure to uncomment the coregen commands in ise_flow.bat or create_ise.bat files in par folder.
   C0_QDRII_MEMORY_WIDTH  : integer := 18; -- # of memory component's data width
   C0_QDRII_SIM_ONLY    : integer := 0; -- = 1 to skip SRAM power up delay
   RST_ACT_LOW          : integer := 1  -- =1 for active low reset, =0 for active high
   );
  port(
   c0_qdr_d              : out   std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_qdr_q              : in    std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_qdr_sa             : out   std_logic_vector((C0_QDRII_ADDR_WIDTH-1) downto 0);
   c0_qdr_w_n            : out   std_logic;
   c0_qdr_r_n            : out   std_logic;
   c0_qdr_dll_off_n      : out   std_logic;
   c0_qdr_bw_n           : out   std_logic_vector((C0_QDRII_BW_WIDTH-1) downto 0);
   c0_compare_error      : out   std_logic;
   sys_rst_n             : in    std_logic;
   c0_cal_done           : out   std_logic;
   dcm_locked            : in    std_logic;
   clk0                  : in    std_logic;
   clk180                : in    std_logic;
   clk270                : in    std_logic;
   clk200                : in    std_logic;
   c0_qdr_cq             : in    std_logic_vector((C0_QDRII_CQ_WIDTH-1) downto 0);
   c0_qdr_cq_n           : in    std_logic_vector((C0_QDRII_CQ_WIDTH-1) downto 0);
   c0_qdr_k              : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_k_n            : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_c              : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_c_n            : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0)
   );
end entity qdrii_sram;

architecture arc_mem_interface_top of qdrii_sram is

  attribute X_CORE_INFO : string;
  attribute X_CORE_INFO of arc_mem_interface_top : ARCHITECTURE IS
    "mig_v2_1_qdrii_sram_v5, Coregen 10.1i_ip0";

  attribute CORE_GENERATION_INFO : string;
  attribute CORE_GENERATION_INFO of arc_mem_interface_top : ARCHITECTURE IS "qdrii_sram_v5,mig_v2_1,{component_name=qdrii_sram_v5, addr_width = 20, burst_length = 4, bw_width = 2, clk_freq = 250, clk_width = 1, cq_width = 1, data_width = 18, memory_width = 18, rst_act_low = 1}";

constant c0_cq_zeros : std_logic_vector(C0_QDRII_CQ_WIDTH-1 downto 0) := (others => '0');

  component qdrii_idelay_ctrl
    port (
      user_rst_200         : in    std_logic;
      idelay_ctrl_rdy      : out   std_logic;
      clk200               : in    std_logic
      );
  end component;

component qdrii_infrastructure
    generic (
      RST_ACT_LOW           : integer

      );
    port (
      sys_rst_n            : in    std_logic;
      dcm_locked           : in    std_logic;
      user_rst_0           : out   std_logic;
      user_rst_180         : out   std_logic;
      user_rst_270         : out   std_logic;
      user_rst_200         : out   std_logic;
      idelay_ctrl_rdy      : in    std_logic;
      clk0                 : in    std_logic;
      clk180               : in    std_logic;
      clk270               : in    std_logic;
      clk200               : in    std_logic

      );
  end component;


component qdrii_top
    generic (
      ADDR_WIDTH   : integer;
      BURST_LENGTH   : integer;
      BW_WIDTH     : integer;
      CLK_FREQ        : integer;
      CLK_WIDTH    : integer;
      CQ_WIDTH     : integer;
      DATA_WIDTH   : integer;
      DEBUG_EN     : integer;
      MEMORY_WIDTH   : integer;
      SIM_ONLY     : integer
      );
    port (
      qdr_d                : out   std_logic_vector((DATA_WIDTH-1) downto 0);
      qdr_q                : in    std_logic_vector((DATA_WIDTH-1) downto 0);
      qdr_sa               : out   std_logic_vector((ADDR_WIDTH-1) downto 0);
      qdr_w_n              : out   std_logic;
      qdr_r_n              : out   std_logic;
      qdr_dll_off_n        : out   std_logic;
      qdr_bw_n             : out   std_logic_vector((BW_WIDTH-1) downto 0);
      cal_done             : out   std_logic;
      user_rst_0           : in    std_logic;
      user_rst_180         : in    std_logic;
      user_rst_270         : in    std_logic;
      idelay_ctrl_rdy      : in   std_logic;
      clk0                 : in    std_logic;
      clk180               : in    std_logic;
      clk270               : in    std_logic;
      user_ad_w_n          : in    std_logic;
      user_d_w_n           : in    std_logic;
      user_r_n             : in    std_logic;
      user_wr_full         : out   std_logic;
      user_rd_full         : out   std_logic;
      user_qr_valid        : out   std_logic;
      user_dwl             : in    std_logic_vector((DATA_WIDTH-1) downto 0);
      user_dwh             : in    std_logic_vector((DATA_WIDTH-1) downto 0);
      user_qrl             : out   std_logic_vector((DATA_WIDTH-1) downto 0);
      user_qrh             : out   std_logic_vector((DATA_WIDTH-1) downto 0);
      user_bwl_n           : in    std_logic_vector((BW_WIDTH-1) downto 0);
      user_bwh_n           : in    std_logic_vector((BW_WIDTH-1) downto 0);
      user_ad_wr           : in    std_logic_vector((ADDR_WIDTH-1) downto 0);
      user_ad_rd           : in    std_logic_vector((ADDR_WIDTH-1) downto 0);
      qdr_cq               : in    std_logic_vector((CQ_WIDTH-1) downto 0);
      qdr_cq_n             : in    std_logic_vector((CQ_WIDTH-1) downto 0);
      qdr_k                : out   std_logic_vector((CLK_WIDTH-1) downto 0);
      qdr_k_n              : out   std_logic_vector((CLK_WIDTH-1) downto 0);
      qdr_c                : out   std_logic_vector((CLK_WIDTH-1) downto 0);
      qdr_c_n              : out   std_logic_vector((CLK_WIDTH-1) downto 0);
      dbg_init_count_done     : out  std_logic;
      dbg_q_cq_init_delay_done   : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_q_cq_n_init_delay_done   : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_q_cq_init_delay_done_tap_count   : out  std_logic_vector((6*CQ_WIDTH)-1 downto 0);
      dbg_q_cq_n_init_delay_done_tap_count   : out  std_logic_vector((6*CQ_WIDTH)-1 downto 0);
      dbg_cq_cal_done         : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_cq_n_cal_done       : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_cq_cal_tap_count    : out  std_logic_vector((6*CQ_WIDTH)-1 downto 0);
      dbg_cq_n_cal_tap_count   : out  std_logic_vector((6*CQ_WIDTH)-1 downto 0);
      dbg_we_cal_done_cq      : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_we_cal_done_cq_n    : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_cq_q_data_valid     : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_cq_n_q_data_valid   : out  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_cal_done            : out  std_logic;
      dbg_data_valid          : out  std_logic;
      dbg_idel_up_all         : in  std_logic;
      dbg_idel_down_all       : in  std_logic;
      dbg_idel_up_q_cq        : in  std_logic;
      dbg_idel_down_q_cq      : in  std_logic;
      dbg_idel_up_q_cq_n      : in  std_logic;
      dbg_idel_down_q_cq_n    : in  std_logic;
      dbg_idel_up_cq          : in  std_logic;
      dbg_idel_down_cq        : in  std_logic;
      dbg_idel_up_cq_n        : in  std_logic;
      dbg_idel_down_cq_n      : in  std_logic;
      dbg_sel_idel_q_cq       : in  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_sel_all_idel_q_cq   : in  std_logic;
      dbg_sel_idel_q_cq_n     : in  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_sel_all_idel_q_cq_n   : in  std_logic;
      dbg_sel_idel_cq         : in  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_sel_all_idel_cq     : in  std_logic;
      dbg_sel_idel_cq_n       : in  std_logic_vector(CQ_WIDTH-1 downto 0);
      dbg_sel_all_idel_cq_n   : in  std_logic

      );
  end component;


component  qdrii_tb_top
    generic (
      ADDR_WIDTH   : integer;
      BURST_LENGTH   : integer;
      BW_WIDTH     : integer;
      DATA_WIDTH   : integer
      );
    port (
      compare_error        : out   std_logic;
      cal_done             : in    std_logic;
      user_rst_0           : in    std_logic;
      clk0                 : in    std_logic;
      user_ad_w_n          : out   std_logic;
      user_d_w_n           : out   std_logic;
      user_r_n             : out   std_logic;
      user_wr_full         : in    std_logic;
      user_rd_full         : in    std_logic;
      user_qr_valid        : in    std_logic;
      user_dwl             : out   std_logic_vector((DATA_WIDTH-1) downto 0);
      user_dwh             : out   std_logic_vector((DATA_WIDTH-1) downto 0);
      user_qrl             : in    std_logic_vector((DATA_WIDTH-1) downto 0);
      user_qrh             : in    std_logic_vector((DATA_WIDTH-1) downto 0);
      user_bwl_n           : out   std_logic_vector((BW_WIDTH-1) downto 0);
      user_bwh_n           : out   std_logic_vector((BW_WIDTH-1) downto 0);
      user_ad_wr           : out   std_logic_vector((ADDR_WIDTH-1) downto 0);
      user_ad_rd           : out   std_logic_vector((ADDR_WIDTH-1) downto 0)
      );
  end component;


  signal  user_rst_0           : std_logic;
  signal  user_rst_180         : std_logic;
  signal  user_rst_270         : std_logic;
  signal  user_rst_200         : std_logic;
  signal  idelay_ctrl_rdy      : std_logic;
  signal  c0_user_ad_w_n       : std_logic;
  signal  c0_user_d_w_n        : std_logic;
  signal  c0_user_r_n          : std_logic;
  signal  c0_user_wr_full      : std_logic;
  signal  c0_user_rd_full      : std_logic;
  signal  c0_user_qr_valid     : std_logic;
  signal  c0_user_dwl          : std_logic_vector((C0_QDRII_DATA_WIDTH)-1 downto 0);
  signal  c0_user_dwh          : std_logic_vector((C0_QDRII_DATA_WIDTH)-1 downto 0);
  signal  c0_user_qrl          : std_logic_vector((C0_QDRII_DATA_WIDTH)-1 downto 0);
  signal  c0_user_qrh          : std_logic_vector((C0_QDRII_DATA_WIDTH)-1 downto 0);
  signal  c0_user_bwl_n        : std_logic_vector((C0_QDRII_BW_WIDTH)-1 downto 0);
  signal  c0_user_bwh_n        : std_logic_vector((C0_QDRII_BW_WIDTH)-1 downto 0);
  signal  c0_user_ad_wr        : std_logic_vector((C0_QDRII_ADDR_WIDTH)-1 downto 0);
  signal  c0_user_ad_rd        : std_logic_vector((C0_QDRII_ADDR_WIDTH)-1 downto 0);
  signal  c0_i_cal_done           : std_logic;

  --Debug Signals

  signal control0     : std_logic_vector(35 downto 0);
  signal dbg_async_in : std_logic_vector(67 downto 0);
  signal dbg_sync_out : std_logic_vector(36 downto 0);


begin

  --***************************************************************************
  c0_cal_done   <= c0_i_cal_done;

  u_qdrii_idelay_ctrl : qdrii_idelay_ctrl
    port map (
      user_rst_200          => user_rst_200,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk200                => clk200
   );


  u_qdrii_infrastructure : qdrii_infrastructure
    generic map (
      RST_ACT_LOW           => RST_ACT_LOW
   )
    port map (
      sys_rst_n             => sys_rst_n,
      dcm_locked            => dcm_locked,
      user_rst_0            => user_rst_0,
      user_rst_180          => user_rst_180,
      user_rst_270          => user_rst_270,
      user_rst_200          => user_rst_200,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk0                  => clk0,
      clk180                => clk180,
      clk270                => clk270,
      clk200                => clk200
   );


  u_qdrii_top_0 : qdrii_top
    generic map (
      ADDR_WIDTH            => C0_QDRII_ADDR_WIDTH,
      BURST_LENGTH          => C0_QDRII_BURST_LENGTH,
      BW_WIDTH              => C0_QDRII_BW_WIDTH,
      CLK_FREQ              => QDRII_CLK_FREQ,
      CLK_WIDTH             => C0_QDRII_CLK_WIDTH,
      CQ_WIDTH              => C0_QDRII_CQ_WIDTH,
      DATA_WIDTH            => C0_QDRII_DATA_WIDTH,
      DEBUG_EN              => C0_QDRII_DEBUG_EN,
      MEMORY_WIDTH          => C0_QDRII_MEMORY_WIDTH,
      SIM_ONLY              => C0_QDRII_SIM_ONLY
      )
    port map (
      qdr_d                 => c0_qdr_d,
      qdr_q                 => c0_qdr_q,
      qdr_sa                => c0_qdr_sa,
      qdr_w_n               => c0_qdr_w_n,
      qdr_r_n               => c0_qdr_r_n,
      qdr_dll_off_n         => c0_qdr_dll_off_n,
      qdr_bw_n              => c0_qdr_bw_n,
      cal_done              => c0_i_cal_done,
      user_rst_0            => user_rst_0,
      user_rst_180          => user_rst_180,
      user_rst_270          => user_rst_270,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk0                  => clk0,
      clk180                => clk180,
      clk270                => clk270,
      user_ad_w_n           => c0_user_ad_w_n,
      user_d_w_n            => c0_user_d_w_n,
      user_r_n              => c0_user_r_n,
      user_wr_full          => c0_user_wr_full,
      user_rd_full          => c0_user_rd_full,
      user_qr_valid         => c0_user_qr_valid,
      user_dwl              => c0_user_dwl,
      user_dwh              => c0_user_dwh,
      user_qrl              => c0_user_qrl,
      user_qrh              => c0_user_qrh,
      user_bwl_n            => c0_user_bwl_n,
      user_bwh_n            => c0_user_bwh_n,
      user_ad_wr            => c0_user_ad_wr,
      user_ad_rd            => c0_user_ad_rd,
      qdr_cq                => c0_qdr_cq,
      qdr_cq_n              => c0_qdr_cq_n,
      qdr_k                 => c0_qdr_k,
      qdr_k_n               => c0_qdr_k_n,
      qdr_c                 => c0_qdr_c,
      qdr_c_n               => c0_qdr_c_n,

      dbg_init_count_done     => open,
      dbg_q_cq_init_delay_done   => open,
      dbg_q_cq_n_init_delay_done   => open,
      dbg_q_cq_init_delay_done_tap_count   => open,
      dbg_q_cq_n_init_delay_done_tap_count   => open,
      dbg_cq_cal_done         => open,
      dbg_cq_n_cal_done       => open,
      dbg_cq_cal_tap_count    => open,
      dbg_cq_n_cal_tap_count   => open,
      dbg_we_cal_done_cq      => open,
      dbg_we_cal_done_cq_n    => open,
      dbg_cq_q_data_valid     => open,
      dbg_cq_n_q_data_valid   => open,
      dbg_cal_done            => open,
      dbg_data_valid          => open,
      dbg_idel_up_all         => '0',
      dbg_idel_down_all       => '0',
      dbg_idel_up_q_cq        => '0',
      dbg_idel_down_q_cq      => '0',
      dbg_idel_up_q_cq_n      => '0',
      dbg_idel_down_q_cq_n    => '0',
      dbg_idel_up_cq          => '0',
      dbg_idel_down_cq        => '0',
      dbg_idel_up_cq_n        => '0',
      dbg_idel_down_cq_n      => '0',
      dbg_sel_idel_q_cq       => c0_cq_zeros,
      dbg_sel_all_idel_q_cq   => '0',
      dbg_sel_idel_q_cq_n     => c0_cq_zeros,
      dbg_sel_all_idel_q_cq_n   => '0',
      dbg_sel_idel_cq         => c0_cq_zeros,
      dbg_sel_all_idel_cq     => '0',
      dbg_sel_idel_cq_n       => c0_cq_zeros,
      dbg_sel_all_idel_cq_n   => '0'
      );

  u_qdrii_tb_top_0 : qdrii_tb_top
    generic map (
      ADDR_WIDTH            => C0_QDRII_ADDR_WIDTH,
      BURST_LENGTH          => C0_QDRII_BURST_LENGTH,
      BW_WIDTH              => C0_QDRII_BW_WIDTH,
      DATA_WIDTH            => C0_QDRII_DATA_WIDTH
      )
    port map (
      compare_error         => c0_compare_error,
      cal_done              => c0_i_cal_done,
      user_rst_0            => user_rst_0,
      clk0                  => clk0,
      user_ad_w_n           => c0_user_ad_w_n,
      user_d_w_n            => c0_user_d_w_n,
      user_r_n              => c0_user_r_n,
      user_wr_full          => c0_user_wr_full,
      user_rd_full          => c0_user_rd_full,
      user_qr_valid         => c0_user_qr_valid,
      user_dwl              => c0_user_dwl,
      user_dwh              => c0_user_dwh,
      user_qrl              => c0_user_qrl,
      user_qrh              => c0_user_qrh,
      user_bwl_n            => c0_user_bwl_n,
      user_bwh_n            => c0_user_bwh_n,
      user_ad_wr            => c0_user_ad_wr,
      user_ad_rd            => c0_user_ad_rd
      );
  
end architecture arc_mem_interface_top;
