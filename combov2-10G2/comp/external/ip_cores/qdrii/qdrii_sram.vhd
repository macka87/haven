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
--   Typically, the user will only instantiate MEM_INTERFACE_TOP in their
--   code, and generate all backend logic (test bench) and all the other infrastructure logic
--    separately.
--   In addition to the memory controller, the module instantiates:
--     1. Reset logic based on user clocks
--     2. IDELAY control block
--
--Revision History:
--   Rev 1.1 - Parameter IODELAY_GRP added. PK. 11/27/08
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;
use work.qdrii_chipscope.all;

entity qdrii_sram is
  generic(
   C0_QDRII_ADDR_WIDTH      : integer := 20; 
                              -- # of memory component address bits.
   C0_QDRII_BURST_LENGTH    : integer := 4; 
                              -- # = 2 -> Burst Length 2 memory part,
                              -- # = 4 -> Burst Length 4 memory part.
   C0_QDRII_BW_WIDTH        : integer := 2; 
                              -- # of Byte Write Control bits.
   F0_QDRII_CLK_PERIOD      : integer := 4000; 
                              -- Core/Memory clock period (in ps).
   C0_QDRII_CLK_WIDTH       : integer := 1; 
                              -- # of memory clock outputs. Represents the
                              -- number of K, K_n, C, and C_n clocks.
   C0_QDRII_CQ_WIDTH        : integer := 1; 
                              -- # of CQ bits.
   C0_QDRII_DATA_WIDTH      : integer := 18; 
                              -- Design Data Width.
   C0_QDRII_DEBUG_EN        : integer := 0; 
                              -- Enable debug signals/controls. When this
                              -- parameter is changed from 0 to 1, make sure to
                              -- uncomment the coregen commands in ise_flow.bat
                              -- or create_ise.bat files in par folder.
   C0_QDRII_HIGH_PERFORMANCE_MODE  : boolean := TRUE; 
                                     -- # = TRUE, the IODELAY performance mode
                                     -- is set to high.
                                     -- # = FALSE, the IODELAY performance mode
                                     -- is set to low.
   C0_QDRII_MEMORY_WIDTH    : integer := 18; 
                              -- # of memory part's data width.
   RST_ACT_LOW              : integer := 1; 
                              -- # = 1 for active low reset, # = 0 for active high.
   C0_QDRII_SIM_ONLY        : integer := 0; 
                              -- # = 1 to skip SRAM power up delay.
   C1_QDRII_ADDR_WIDTH      : integer := 20; 
                              -- # of memory component address bits.
   C1_QDRII_BURST_LENGTH    : integer := 4; 
                              -- # = 2 -> Burst Length 2 memory part,
                              -- # = 4 -> Burst Length 4 memory part.
   C1_QDRII_BW_WIDTH        : integer := 2; 
                              -- # of Byte Write Control bits.
   C1_QDRII_CLK_WIDTH       : integer := 1; 
                              -- # of memory clock outputs. Represents the
                              -- number of K, K_n, C, and C_n clocks.
   C1_QDRII_CQ_WIDTH        : integer := 1; 
                              -- # of CQ bits.
   C1_QDRII_DATA_WIDTH      : integer := 18; 
                              -- Design Data Width.
   C1_QDRII_DEBUG_EN        : integer := 0; 
                              -- Enable debug signals/controls. When this
                              -- parameter is changed from 0 to 1, make sure to
                              -- uncomment the coregen commands in ise_flow.bat
                              -- or create_ise.bat files in par folder.
   C1_QDRII_HIGH_PERFORMANCE_MODE  : boolean := TRUE; 
                                     -- # = TRUE, the IODELAY performance mode
                                     -- is set to high.
                                     -- # = FALSE, the IODELAY performance mode
                                     -- is set to low.
   C1_QDRII_MEMORY_WIDTH    : integer := 18; 
                              -- # of memory part's data width.
   C1_QDRII_SIM_ONLY        : integer := 0  
                              -- # = 1 to skip SRAM power up delay.
   );
  port(
   c0_qdr_d              : out   std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_qdr_q              : in    std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_qdr_sa             : out   std_logic_vector((C0_QDRII_ADDR_WIDTH-1) downto 0);
   c0_qdr_w_n            : out   std_logic;
   c0_qdr_r_n            : out   std_logic;
   c0_qdr_dll_off_n      : out   std_logic;
   c0_qdr_bw_n           : out   std_logic_vector((C0_QDRII_BW_WIDTH-1) downto 0);
   sys_rst_n             : in    std_logic;
   c0_cal_done           : out   std_logic;
   f0_qdrii_locked       : in    std_logic;
   f0_user_rst_0_tb               : out   std_logic;
   f0_qdrii_clk0         : in    std_logic;
   f0_qdrii_clk0_tb               : out   std_logic;
   f0_qdrii_clk270       : in    std_logic;
   clk200                : in    std_logic;
   c0_user_ad_w_n        : in    std_logic;
   c0_user_d_w_n         : in    std_logic;
   c0_user_r_n           : in    std_logic;
   c0_user_wr_full       : out   std_logic;
   c0_user_rd_full       : out   std_logic;
   c0_user_qr_valid      : out   std_logic;
   c0_user_dwl           : in    std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_user_dwh           : in    std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_user_qrl           : out   std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_user_qrh           : out   std_logic_vector((C0_QDRII_DATA_WIDTH-1) downto 0);
   c0_user_bwl_n         : in    std_logic_vector((C0_QDRII_BW_WIDTH-1) downto 0);
   c0_user_bwh_n         : in    std_logic_vector((C0_QDRII_BW_WIDTH-1) downto 0);
   c0_user_ad_wr         : in    std_logic_vector((C0_QDRII_ADDR_WIDTH-1) downto 0);
   c0_user_ad_rd         : in    std_logic_vector((C0_QDRII_ADDR_WIDTH-1) downto 0);
   c0_qdr_cq             : in    std_logic_vector((C0_QDRII_CQ_WIDTH-1) downto 0);
   c0_qdr_cq_n           : in    std_logic_vector((C0_QDRII_CQ_WIDTH-1) downto 0);
   c0_qdr_k              : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_k_n            : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_c              : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c0_qdr_c_n            : out   std_logic_vector((C0_QDRII_CLK_WIDTH-1) downto 0);
   c1_qdr_d              : out   std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_qdr_q              : in    std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_qdr_sa             : out   std_logic_vector((C1_QDRII_ADDR_WIDTH-1) downto 0);
   c1_qdr_w_n            : out   std_logic;
   c1_qdr_r_n            : out   std_logic;
   c1_qdr_dll_off_n      : out   std_logic;
   c1_qdr_bw_n           : out   std_logic_vector((C1_QDRII_BW_WIDTH-1) downto 0);
   c1_cal_done           : out   std_logic;
   c1_user_ad_w_n        : in    std_logic;
   c1_user_d_w_n         : in    std_logic;
   c1_user_r_n           : in    std_logic;
   c1_user_wr_full       : out   std_logic;
   c1_user_rd_full       : out   std_logic;
   c1_user_qr_valid      : out   std_logic;
   c1_user_dwl           : in    std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_user_dwh           : in    std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_user_qrl           : out   std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_user_qrh           : out   std_logic_vector((C1_QDRII_DATA_WIDTH-1) downto 0);
   c1_user_bwl_n         : in    std_logic_vector((C1_QDRII_BW_WIDTH-1) downto 0);
   c1_user_bwh_n         : in    std_logic_vector((C1_QDRII_BW_WIDTH-1) downto 0);
   c1_user_ad_wr         : in    std_logic_vector((C1_QDRII_ADDR_WIDTH-1) downto 0);
   c1_user_ad_rd         : in    std_logic_vector((C1_QDRII_ADDR_WIDTH-1) downto 0);
   c1_qdr_cq             : in    std_logic_vector((C1_QDRII_CQ_WIDTH-1) downto 0);
   c1_qdr_cq_n           : in    std_logic_vector((C1_QDRII_CQ_WIDTH-1) downto 0);
   c1_qdr_k              : out   std_logic_vector((C1_QDRII_CLK_WIDTH-1) downto 0);
   c1_qdr_k_n            : out   std_logic_vector((C1_QDRII_CLK_WIDTH-1) downto 0);
   c1_qdr_c              : out   std_logic_vector((C1_QDRII_CLK_WIDTH-1) downto 0);
   c1_qdr_c_n            : out   std_logic_vector((C1_QDRII_CLK_WIDTH-1) downto 0)
   );
end entity qdrii_sram;

architecture arc_mem_interface_top of qdrii_sram is

  attribute X_CORE_INFO : string;
  attribute X_CORE_INFO of arc_mem_interface_top : ARCHITECTURE IS
    "mig_v3_3_qdrii_v5, Coregen 11.4";

  attribute CORE_GENERATION_INFO : string;
  attribute CORE_GENERATION_INFO of arc_mem_interface_top : ARCHITECTURE IS "qdrii_v5,mig_v3_3,{component_name=qdrii_sram, C0_ADDR_WIDTH=20, C0_BURST_LENGTH=4, C0_BW_WIDTH=2, C0_CLK_FREQ=250, F0_CLK_PERIOD=4000, C0_CLK_WIDTH=1, C0_CQ_WIDTH=1, C0_DATA_WIDTH=18, C0_MEMORY_WIDTH=18, RST_ACT_LOW=1, C0_INTERFACE_TYPE=QDRII_SRAM,C1_ADDR_WIDTH=20, C1_BURST_LENGTH=4, C1_BW_WIDTH=2, C1_CLK_FREQ=250, F0_CLK_PERIOD=4000, C1_CLK_WIDTH=1, C1_CQ_WIDTH=1, C1_DATA_WIDTH=18, C1_MEMORY_WIDTH=18, RST_ACT_LOW=1, C1_INTERFACE_TYPE=QDRII_SRAM, LANGUAGE=VHDL, SYNTHESIS_TOOL=XST, NO_OF_CONTROLLERS=2}";

  --***************************************************************************
  -- IODELAY Group Name: Replication and placement of IDELAYCTRLs will be
  -- handled automatically by software tools if IDELAYCTRLs have same refclk,
  -- reset and rdy nets. Designs with a unique RESET will commonly create a
  -- unique RDY. Constraint IODELAY_GROUP is associated to a set of IODELAYs
  -- with an IDELAYCTRL. The parameter IODELAY_GRP value can be any string.
  --***************************************************************************
  constant IODELAY_GRP : string := "IODELAY_MIG";

  constant c0_cq_zeros : std_logic_vector(C0_QDRII_CQ_WIDTH-1 downto 0) := (others => '0');
  constant c1_cq_zeros : std_logic_vector(C1_QDRII_CQ_WIDTH-1 downto 0) := (others => '0');

  component qdrii_idelay_ctrl
    generic (
      IODELAY_GRP       : string
      );
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
      locked               : in    std_logic;
      user_rst_0           : out   std_logic;
      user_rst_180         : out   std_logic;
      user_rst_270         : out   std_logic;
      user_rst_200         : out   std_logic;
      idelay_ctrl_rdy      : in    std_logic;
      clk0                 : in    std_logic;
      clk180               : out   std_logic;
      clk270               : in    std_logic;
      clk200               : in    std_logic

      );
  end component;


component qdrii_top
    generic (
      ADDR_WIDTH   : integer;
      BURST_LENGTH   : integer;
      BW_WIDTH     : integer;
      CLK_PERIOD   : integer;
      CLK_WIDTH    : integer;
      CQ_WIDTH     : integer;
      DATA_WIDTH   : integer;
      DEBUG_EN     : integer;
      HIGH_PERFORMANCE_MODE   : boolean;
      IODELAY_GRP           : string;
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




  signal  f0_user_rst_0          : std_logic;
  signal  f0_user_rst_180        : std_logic;
  signal  f0_user_rst_270        : std_logic;
  signal  user_rst_200           : std_logic;
  signal  idelay_ctrl_rdy        : std_logic;
  signal  f0_qdrii_clk180        : std_logic;
  signal  c0_i_cal_done           : std_logic;


  signal  c1_i_cal_done           : std_logic;






begin

  --***************************************************************************
  f0_user_rst_0_tb <= f0_user_rst_0;
  f0_qdrii_clk0_tb <= f0_qdrii_clk0;
  c0_cal_done   <= c0_i_cal_done;
  c1_cal_done   <= c1_i_cal_done;





  u_qdrii_idelay_ctrl : qdrii_idelay_ctrl
    generic map (
      IODELAY_GRP        => IODELAY_GRP
   )
    port map (
      user_rst_200          => user_rst_200,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk200                => clk200
   );


u_qdrii_infrastructure_f0 :qdrii_infrastructure
    generic map (
      RST_ACT_LOW           => RST_ACT_LOW
   )
    port map (
      sys_rst_n             => sys_rst_n,
      locked                => f0_qdrii_locked,
      user_rst_0            => f0_user_rst_0,
      user_rst_180          => f0_user_rst_180,
      user_rst_270          => f0_user_rst_270,
      user_rst_200          => user_rst_200,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk0                  => f0_qdrii_clk0,
      clk180                => f0_qdrii_clk180,
      clk270                => f0_qdrii_clk270,
      clk200                => clk200
   );


  u_qdrii_top_0 : qdrii_top
    generic map (
      ADDR_WIDTH            => C0_QDRII_ADDR_WIDTH,
      BURST_LENGTH          => C0_QDRII_BURST_LENGTH,
      BW_WIDTH              => C0_QDRII_BW_WIDTH,
      CLK_PERIOD            => F0_QDRII_CLK_PERIOD,
      CLK_WIDTH             => C0_QDRII_CLK_WIDTH,
      CQ_WIDTH              => C0_QDRII_CQ_WIDTH,
      DATA_WIDTH            => C0_QDRII_DATA_WIDTH,
      DEBUG_EN              => C0_QDRII_DEBUG_EN,
      HIGH_PERFORMANCE_MODE   => C0_QDRII_HIGH_PERFORMANCE_MODE,
      IODELAY_GRP           => IODELAY_GRP,
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
      user_rst_0            => f0_user_rst_0,
      user_rst_180          => f0_user_rst_180,
      user_rst_270          => f0_user_rst_270,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk0                  => f0_qdrii_clk0,
      clk180                => f0_qdrii_clk180,
      clk270                => f0_qdrii_clk270,
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
  u_qdrii_top_1 : qdrii_top
    generic map (
      ADDR_WIDTH            => C1_QDRII_ADDR_WIDTH,
      BURST_LENGTH          => C1_QDRII_BURST_LENGTH,
      BW_WIDTH              => C1_QDRII_BW_WIDTH,
      CLK_WIDTH             => C1_QDRII_CLK_WIDTH,
      CQ_WIDTH              => C1_QDRII_CQ_WIDTH,
      DATA_WIDTH            => C1_QDRII_DATA_WIDTH,
      DEBUG_EN              => C1_QDRII_DEBUG_EN,
      HIGH_PERFORMANCE_MODE   => C1_QDRII_HIGH_PERFORMANCE_MODE,
      IODELAY_GRP           => IODELAY_GRP,
      MEMORY_WIDTH          => C1_QDRII_MEMORY_WIDTH,
      CLK_PERIOD            => F0_qdrii_CLK_PERIOD,
      SIM_ONLY              => C1_QDRII_SIM_ONLY
      )
    port map (
      qdr_d                 => c1_qdr_d,
      qdr_q                 => c1_qdr_q,
      qdr_sa                => c1_qdr_sa,
      qdr_w_n               => c1_qdr_w_n,
      qdr_r_n               => c1_qdr_r_n,
      qdr_dll_off_n         => c1_qdr_dll_off_n,
      qdr_bw_n              => c1_qdr_bw_n,
      cal_done              => c1_i_cal_done,
      user_rst_0            => f0_user_rst_0,
      user_rst_180          => f0_user_rst_180,
      user_rst_270          => f0_user_rst_270,
      idelay_ctrl_rdy       => idelay_ctrl_rdy,
      clk0                  => f0_qdrii_clk0,
      clk180                => f0_qdrii_clk180,
      clk270                => f0_qdrii_clk270,
      user_ad_w_n           => c1_user_ad_w_n,
      user_d_w_n            => c1_user_d_w_n,
      user_r_n              => c1_user_r_n,
      user_wr_full          => c1_user_wr_full,
      user_rd_full          => c1_user_rd_full,
      user_qr_valid         => c1_user_qr_valid,
      user_dwl              => c1_user_dwl,
      user_dwh              => c1_user_dwh,
      user_qrl              => c1_user_qrl,
      user_qrh              => c1_user_qrh,
      user_bwl_n            => c1_user_bwl_n,
      user_bwh_n            => c1_user_bwh_n,
      user_ad_wr            => c1_user_ad_wr,
      user_ad_rd            => c1_user_ad_rd,
      qdr_cq                => c1_qdr_cq,
      qdr_cq_n              => c1_qdr_cq_n,
      qdr_k                 => c1_qdr_k,
      qdr_k_n               => c1_qdr_k_n,
      qdr_c                 => c1_qdr_c,
      qdr_c_n               => c1_qdr_c_n,

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
      dbg_sel_idel_q_cq       => c1_cq_zeros,
      dbg_sel_all_idel_q_cq   => '0',
      dbg_sel_idel_q_cq_n     => c1_cq_zeros,
      dbg_sel_all_idel_q_cq_n   => '0',
      dbg_sel_idel_cq         => c1_cq_zeros,
      dbg_sel_all_idel_cq     => '0',
      dbg_sel_idel_cq_n       => c1_cq_zeros,
      dbg_sel_all_idel_cq_n   => '0'
      );






end architecture arc_mem_interface_top;
