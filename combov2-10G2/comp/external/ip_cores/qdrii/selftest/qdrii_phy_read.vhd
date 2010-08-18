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
--  /   /         Filename           : qdrii_phy_read.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Is the top level module for read capture.
--  2. Instantiates the I/O modules for the memory clock and data, the
--     initialization state machine, the delay calibration state machine,
--         the write enable state machine as well as generating the read
--     commands to the memory.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_phy_read is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4;
    CLK_FREQ     : integer := 300;
    CQ_WIDTH     : integer := 2;
    DATA_WIDTH   : integer := 72;
    DEBUG_EN     : integer := 0;
    MEMORY_WIDTH : integer := 36;
    Q_PER_CQ     : integer := 18;
    Q_PER_CQ_9   : integer := 2;
    SIM_ONLY     : integer := 0
    );
  port(
    clk0                                 : in  std_logic;
    clk180                               : in  std_logic;
    clk270                               : in  std_logic;
    user_rst_0                           : in  std_logic;
    user_rst_180                         : in  std_logic;
    user_rst_270                         : in  std_logic;
    idly_ctrl_rdy                        : in  std_logic;
    rd_init_n                            : in  std_logic;
    qdr_q                                : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    qdr_cq                               : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    qdr_cq_n                             : in  std_logic_vector(CQ_WIDTH-1 downto 0);
    read_data_rise                       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    read_data_fall                       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    data_valid                           : out std_logic;
    dummy_write                          : out std_logic_vector(1 downto 0);
    dummy_read                           : out std_logic_vector(1 downto 0);
    cal_done                             : out std_logic;
    init_cnt_done                        : out std_logic;
    qdr_r_n                              : out std_logic;
    rd_init_delay_n                      : out std_logic;
    rd_init_delay2_n                     : out std_logic;
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
    dbg_cal_done                         : out std_logic
    );
end entity qdrii_phy_read;

architecture arch_qdrii_phy_read of qdrii_phy_read is

  constant STROBE_WIDTH : integer := ((CQ_WIDTH*(MEMORY_WIDTH/36))+CQ_WIDTH);
  -- For a 36 bit component design the value is 2*CQ_WIDTH, for 18 bit component
  -- designs the value is CQ_WIDTH. For x36 bit component designs, both CQ and
  -- CQ# are used in calibration. For x18 bit component designs, only CQ is used
  -- in calibration.

  constant ones : std_logic_vector(CQ_WIDTH-1 downto 0) := (others =>'1');

  signal qdr_r_n_int                 : std_logic;
  signal rd_cmd_in                   : std_logic;
  signal dly_cal_start               : std_logic;
  signal dly_cal_done                : std_logic;
  signal we_cal_start                : std_logic;
  signal we_cal_done                 : std_logic;
  signal cal_done_i                  : std_logic;
  signal q_init_delay_done           : std_logic;
  signal dummy_read_i                : std_logic_vector(1 downto 0);
  signal rd_init_delay3_n            : std_logic;
  signal rd_init_delay2_n_i          : std_logic;
  signal rd_init_delay_n_i           : std_logic;
  signal init_cnt_done_i             : std_logic;
  signal data_valid_out              : std_logic;
  signal q_init_delay_done_cq_inst   : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_init_delay_done_cq_n_inst : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_dly_ce                 : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_n_dly_ce               : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_dly_inc                : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_n_dly_inc              : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_dly_rst                : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal q_cq_n_dly_rst              : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_dly_ce                   : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_n_dly_ce                 : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_dly_inc                  : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_n_dly_inc                : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_dly_rst                  : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal cq_n_dly_rst                : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal rd_data_rise                : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal rd_data_fall                : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal rd_data_rise_out            : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal rd_data_fall_out            : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dly_cal_done_cq_inst        : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal dly_cal_done_cq_n_inst      : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal data_valid_inst             : std_logic_vector(STROBE_WIDTH-1 downto 0);
  signal data_valid_cq_inst          : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal data_valid_cq_n_inst        : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal we_cal_done_cq_inst         : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal we_cal_done_cq_n_inst       : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal qdr_cq_bufio                : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal qdr_cq_n_bufio              : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal not_qdr_cq_bufio            : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal unused_qdr_cq_n             : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal srl_count                   : std_logic_vector((STROBE_WIDTH*4)-1 downto 0);
  signal dbg_sel_idel_q_cq_i         : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal dbg_sel_idel_q_cq_n_i       : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal dbg_sel_idel_cq_i           : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal dbg_sel_idel_cq_n_i         : std_logic_vector(CQ_WIDTH-1 downto 0);
  signal dbg_idel_up_q_cq_i          : std_logic;
  signal dbg_idel_down_q_cq_i        : std_logic;
  signal dbg_idel_up_q_cq_n_i        : std_logic;
  signal dbg_idel_down_q_cq_n_i      : std_logic;
  signal dbg_idel_up_cq_i            : std_logic;
  signal dbg_idel_down_cq_i          : std_logic;
  signal dbg_idel_up_cq_n_i          : std_logic;
  signal dbg_idel_down_cq_n_i        : std_logic;

  component qdrii_phy_cq_io
    port(
      qdr_cq       : in  std_logic;
      cal_clk      : in  std_logic;
      cq_dly_ce    : in  std_logic;
      cq_dly_inc   : in  std_logic;
      cq_dly_rst   : in  std_logic;
      qdr_cq_bufio : out std_logic
      );
  end component qdrii_phy_cq_io;

  component qdrii_phy_q_io
    generic(
      DATA_WIDTH : integer := DATA_WIDTH;
      CQ_WIDTH   : integer := CQ_WIDTH;
      Q_PER_CQ   : integer := Q_PER_CQ
      );
    port(
      qdr_q      : in  std_logic_vector(Q_PER_CQ-1 downto 0);
      bufio_clk  : in  std_logic;
      q_dly_ce   : in  std_logic;
      q_dly_inc  : in  std_logic;
      q_dly_rst  : in  std_logic;
      cal_clk    : in  std_logic;
      qdr_q_rise : out std_logic_vector(Q_PER_CQ-1 downto 0);
      qdr_q_fall : out std_logic_vector(Q_PER_CQ-1 downto 0)
      );
  end component qdrii_phy_q_io;

  component qdrii_phy_init_sm
    generic(
      BURST_LENGTH : integer := BURST_LENGTH;
      SIM_ONLY     : integer := SIM_ONLY;
      CLK_FREQ     : integer := CLK_FREQ
      );
    port(
      clk0              : in  std_logic;
      user_rst_0        : in  std_logic;
      dly_cal_done      : in  std_logic;
      q_init_delay_done : in  std_logic;
      en_cal_done       : in  std_logic;
      dly_ready         : in  std_logic;
      dly_cal_start     : out std_logic;
      we_cal_start      : out std_logic;
      dummy_write       : out std_logic_vector(1 downto 0);
      dummy_read        : out std_logic_vector(1 downto 0);
      cal_done          : out std_logic;
      init_cnt_done     : out std_logic
      );
  end component qdrii_phy_init_sm;

  component qdrii_phy_dly_cal_sm
    generic(
       BURST_LENGTH : integer := BURST_LENGTH;
       CLK_FREQ     : integer := CLK_FREQ;
       CQ_WIDTH     : integer := CQ_WIDTH;
       DATA_WIDTH   : integer := DATA_WIDTH;
       DEBUG_EN     : integer := DEBUG_EN;
       Q_PER_CQ     : integer := Q_PER_CQ;
       Q_PER_CQ_9   : integer := Q_PER_CQ_9
       );
    port(
      clk0                            : in  std_logic;
      user_rst_0                      : in  std_logic;
      start_cal                       : in  std_logic;
      rd_data_rise                    : in  std_logic_vector(Q_PER_CQ-1 downto 0);
      rd_data_fall                    : in  std_logic_vector(Q_PER_CQ-1 downto 0);
      q_delay_done                    : in  std_logic;
      rd_en                           : in  std_logic;
      we_cal_start                    : in  std_logic;
      q_dly_rst                       : out std_logic;
      q_dly_ce                        : out std_logic;
      q_dly_inc                       : out std_logic;
      cq_dly_rst                      : out std_logic;
      cq_dly_ce                       : out std_logic;
      cq_dly_inc                      : out std_logic;
      dly_cal_done                    : out std_logic;
      q_init_delay_done               : out std_logic;
      rdfifo_we                       : out std_logic;
      we_cal_done                     : out std_logic;
      srl_count                       : out std_logic_vector(3 downto 0);
      -- Debug Signals
      dbg_idel_up_q_cq                : in  std_logic;
      dbg_idel_down_q_cq              : in  std_logic;
      dbg_idel_up_cq                  : in  std_logic;
      dbg_idel_down_cq                : in  std_logic;
      dbg_sel_idel_q_cq               : in  std_logic;
      dbg_sel_idel_cq                 : in  std_logic;
      dbg_q_init_delay_done_tap_count : out std_logic_vector(5 downto 0);
      dbg_cq_cal_tap_count            : out std_logic_vector(5 downto 0)
      );
  end component qdrii_phy_dly_cal_sm;

 component qdrii_phy_en is
  generic(
     DATA_WIDTH   : integer := DATA_WIDTH;
     CQ_WIDTH     : integer := CQ_WIDTH;
     Q_PER_CQ     : integer := Q_PER_CQ;
     STROBE_WIDTH : integer := STROBE_WIDTH
     );
  port(
    clk0              : in  std_logic;
    user_rst_0        : in  std_logic;
    we_cal_done       : in  std_logic;
    rd_data_rise      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    rd_data_fall      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    we_in             : in  std_logic_vector(STROBE_WIDTH-1 downto 0);
    srl_count         : in  std_logic_vector((STROBE_WIDTH*4)-1 downto 0);
    rd_data_rise_out  : out std_logic_vector(DATA_WIDTH-1 downto 0);
    rd_data_fall_out  : out std_logic_vector(DATA_WIDTH-1 downto 0);
    data_valid_out    : out std_logic
    );
end component qdrii_phy_en;

  attribute syn_useioff : boolean;
  attribute IOB : string;
  attribute keep : string;
  attribute S : string;
  attribute syn_noprune : boolean;
  attribute syn_keep : boolean;

  attribute keep of unused_qdr_cq_n : signal is "true";
  attribute S of qdr_cq_n : signal is "TRUE";
  attribute syn_keep of unused_qdr_cq_n : signal is true;
  attribute syn_keep of qdr_cq_n : signal is true;

begin

  ------------------------------------------------------------------------------
  -- This logic is added to increment/decrement the tap delay count of CQ, CQ#
  -- and the respective Data(Q) bits associated with CQ/CQ# manually. You can
  -- increment/decrement the tap delay values for CQ/CQ# and the corresponding
  -- Data(Q) bits individually or all-together based on the input selection.
  -- You can increment/decrement the tap delay values through VIO (Virtual I/O)
  -- module of Chipscope. Refer to the MIG user guide for more information on
  -- debug port signals.
  --
  -- Note: For QDRII, idelay tap count values are applied on all the Data(Q)
  -- bits which are associated with the correspondng CQ/CQ#. You cannot change
  -- the tap value for each individual Data(Q) bit.
  ------------------------------------------------------------------------------

  dbg_sel_idel_q_cq_i <= (others => '1') when ((dbg_idel_up_all = '1') or
                                               (dbg_idel_down_all = '1') or
                                               (dbg_sel_all_idel_q_cq = '1'))
                                         else
                         dbg_sel_idel_q_cq;

  dbg_sel_idel_q_cq_n_i <= (others => '1') when ((dbg_idel_up_all = '1') or
                                                 (dbg_idel_down_all = '1') or
                                                 (dbg_sel_all_idel_q_cq_n = '1'))
                                           else
                           dbg_sel_idel_q_cq_n;

  dbg_sel_idel_cq_i <= (others => '1') when ((dbg_idel_up_all = '1') or
                                             (dbg_idel_down_all = '1') or
                                             (dbg_sel_all_idel_cq = '1'))
                                       else
                       dbg_sel_idel_cq;

  dbg_sel_idel_cq_n_i <= (others => '1') when ((dbg_idel_up_all = '1') or
                                               (dbg_idel_down_all = '1') or
                                               (dbg_sel_all_idel_cq_n = '1'))
                                         else
                         dbg_sel_idel_cq_n;

  dbg_idel_up_q_cq_i     <= dbg_idel_up_all or dbg_idel_up_q_cq;
  dbg_idel_down_q_cq_i   <= dbg_idel_down_all or dbg_idel_down_q_cq;
  dbg_idel_up_q_cq_n_i   <= dbg_idel_up_all or dbg_idel_up_q_cq_n;
  dbg_idel_down_q_cq_n_i <= dbg_idel_down_all or dbg_idel_down_q_cq_n;
  dbg_idel_up_cq_i       <= dbg_idel_up_all or dbg_idel_up_cq;
  dbg_idel_down_cq_i     <= dbg_idel_down_all or dbg_idel_down_cq;
  dbg_idel_up_cq_n_i     <= dbg_idel_up_all or dbg_idel_up_cq_n;
  dbg_idel_down_cq_n_i   <= dbg_idel_down_all or dbg_idel_down_cq_n;



  dbg_q_cq_init_delay_done   <= q_init_delay_done_cq_inst;
  dbg_q_cq_n_init_delay_done <= q_init_delay_done_cq_n_inst;

  dbg_cq_cal_done   <= dly_cal_done_cq_inst;
  dbg_cq_n_cal_done <= dly_cal_done_cq_n_inst;

  dbg_we_cal_done_cq   <= we_cal_done_cq_inst;
  dbg_we_cal_done_cq_n <= we_cal_done_cq_n_inst;

  dbg_cq_q_data_valid   <= data_valid_cq_inst;
  dbg_cq_n_q_data_valid <= data_valid_cq_n_inst;

  dbg_cal_done <= cal_done_i;

  cal_done <= cal_done_i;

  read_data_rise <= rd_data_rise_out;
  read_data_fall <= rd_data_fall_out;

  data_valid <= data_valid_out;
  dummy_read <= dummy_read_i;

  D_V_36 : if(MEMORY_WIDTH = 36) generate
    D_V_SIG : for we_i in 0 to CQ_WIDTH-1 generate
      data_valid_inst(((2*we_i)+1) downto (2*we_i)) <= (data_valid_cq_n_inst(we_i) &
                                                   data_valid_cq_inst(we_i));
    end generate D_V_SIG;
  end generate D_V_36;

  D_V_18_9 : if(MEMORY_WIDTH /= 36) generate
    data_valid_inst <= data_valid_cq_inst;
  end generate D_V_18_9;

  FLAG_36 : if(MEMORY_WIDTH = 36) generate
    dly_cal_done      <= '1' when ((dly_cal_done_cq_inst = ones) and
                                   (dly_cal_done_cq_n_inst = ones)) else
                         '0';
    we_cal_done       <= '1' when ((we_cal_done_cq_inst = ones) and
                                   (we_cal_done_cq_n_inst = ones)) else
                         '0';
    q_init_delay_done <= '1' when ((q_init_delay_done_cq_inst = ones) and
                                   (q_init_delay_done_cq_n_inst = ones)) else
                         '0';
  end generate FLAG_36;

  FLAG_18_9 : if(MEMORY_WIDTH /= 36) generate
    dly_cal_done      <= '1' when (dly_cal_done_cq_inst = ones) else '0';
    we_cal_done       <= '1' when (we_cal_done_cq_inst = ones) else '0';
    q_init_delay_done <= '1' when (q_init_delay_done_cq_inst = ones) else '0';
  end generate FLAG_18_9;

  init_cnt_done  <= init_cnt_done_i;

  CQ_INST_36 : if(MEMORY_WIDTH = 36) generate
    CQ_INST : for cq_i in 0 to CQ_WIDTH-1 generate
      U_QDRII_PHY_CQ_IO : qdrii_phy_cq_io
        port map(
          qdr_cq       => qdr_cq(cq_i),
          cal_clk      => clk0,
          cq_dly_ce    => cq_dly_ce(cq_i),
          cq_dly_inc   => cq_dly_inc(cq_i),
          cq_dly_rst   => cq_dly_rst(cq_i),
          qdr_cq_bufio => qdr_cq_bufio(cq_i)
          );
    end generate CQ_INST;

    CQ_N_INST : for cq_n_i in 0 to CQ_WIDTH-1 generate
      U_QDRII_PHY_CQ_N_IO : qdrii_phy_cq_io
        port map(
          qdr_cq       => qdr_cq_n(cq_n_i),
          cal_clk      => clk0,
          cq_dly_ce    => cq_n_dly_ce(cq_n_i),
          cq_dly_inc   => cq_n_dly_inc(cq_n_i),
          cq_dly_rst   => cq_n_dly_rst(cq_n_i),
          qdr_cq_bufio => qdr_cq_n_bufio(cq_n_i)
          );
    end generate CQ_N_INST;
  end generate CQ_INST_36;

  CQ_INST_18_9 : if(MEMORY_WIDTH /= 36) generate
    CQ_INST : for cq_i in 0 to CQ_WIDTH-1 generate
    attribute syn_noprune of UNUSED_CQ_N_INST : label is true;
    begin
      U_QDRII_PHY_CQ_IO : qdrii_phy_cq_io
        port map(
          qdr_cq       => qdr_cq(cq_i),
          cal_clk      => clk0,
          cq_dly_ce    => cq_dly_ce(cq_i),
          cq_dly_inc   => cq_dly_inc(cq_i),
          cq_dly_rst   => cq_dly_rst(cq_i),
          qdr_cq_bufio => qdr_cq_bufio(cq_i)
          );

      UNUSED_CQ_N_INST : MUXCY
        port map (
          O  => unused_qdr_cq_n(cq_i),
          CI => qdr_cq_n(cq_i),
          DI => '0',
          S  => '1'
          );
    end generate CQ_INST;
  end generate CQ_INST_18_9;

   -----------------------------------------------------------------------------
   -- QDR Q IO instantiations
   -----------------------------------------------------------------------------
   --clocked by CQ_0_P(BYTES 0,2)

  ASGN : for cqwidth in 0 to CQ_WIDTH-1 generate
    not_qdr_cq_bufio(cqwidth) <= not(qdr_cq_bufio(cqwidth));
  end generate ASGN;

  COMP_36_INST : if(MEMORY_WIDTH = 36) generate
    Q_INST_CQ : for cq_w in 0 to CQ_WIDTH-1 generate
      U_QDRII_PHY_Q_IO_CQ : qdrii_phy_q_io
         generic map(
           DATA_WIDTH => DATA_WIDTH,
           CQ_WIDTH   => CQ_WIDTH,
           Q_PER_CQ   => Q_PER_CQ
           )
         port map(
           qdr_q      => qdr_q((((2*cq_w)+1)*Q_PER_CQ)-1 downto (Q_PER_CQ*2*cq_w)),
           bufio_clk  => not_qdr_cq_bufio(cq_w),
           q_dly_ce   => q_cq_dly_ce(cq_w),
           q_dly_inc  => q_cq_dly_inc(cq_w),
           q_dly_rst  => q_cq_dly_rst(cq_w),
           cal_clk    => clk0,
           qdr_q_rise => rd_data_rise((((2*cq_w)+1)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*2*cq_w)),
           qdr_q_fall => rd_data_fall((((2*cq_w)+1)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*2*cq_w))
           );

      U_QDRII_PHY_Q_IO_CQ_N : qdrii_phy_q_io
         generic map(
           DATA_WIDTH => DATA_WIDTH,
           CQ_WIDTH   => CQ_WIDTH,
           Q_PER_CQ   => Q_PER_CQ
           )
         port map(
           qdr_q      => qdr_q((((2*cq_w)+2)*Q_PER_CQ)-1 downto (Q_PER_CQ*((2*cq_w)+1))),
           bufio_clk  => qdr_cq_n_bufio(cq_w),
           q_dly_ce   => q_cq_n_dly_ce(cq_w),
           q_dly_inc  => q_cq_n_dly_inc(cq_w),
           q_dly_rst  => q_cq_n_dly_rst(cq_w),
           cal_clk    => clk0,
           qdr_q_rise => rd_data_rise((((2*cq_w)+2)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*((2*cq_w)+1))),
           qdr_q_fall => rd_data_fall((((2*cq_w)+2)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*((2*cq_w)+1)))
           );
    end generate Q_INST_CQ;
  end generate COMP_36_INST;

  COMP_18_9_INST : if(MEMORY_WIDTH /= 36) generate
    Q_INST_CQ : for cq_w in 0 to CQ_WIDTH-1 generate
      U_QDRII_PHY_Q_IO_CQ : qdrii_phy_q_io
         generic map(
           DATA_WIDTH => DATA_WIDTH,
           CQ_WIDTH   => CQ_WIDTH,
           Q_PER_CQ   => Q_PER_CQ
           )
         port map(
           qdr_q      => qdr_q(((cq_w+1)*Q_PER_CQ)-1 downto (Q_PER_CQ*cq_w)),
           bufio_clk  => not_qdr_cq_bufio(cq_w),
           q_dly_ce   => q_cq_dly_ce(cq_w),
           q_dly_inc  => q_cq_dly_inc(cq_w),
           q_dly_rst  => q_cq_dly_rst(cq_w),
           cal_clk    => clk0,
           qdr_q_rise => rd_data_rise(((cq_w+1)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*cq_w)),
           qdr_q_fall => rd_data_fall(((cq_w+1)*Q_PER_CQ)-1 downto
                                      (Q_PER_CQ*cq_w))
           );
    end generate Q_INST_CQ;
  end generate COMP_18_9_INST;

 -------------------------------------------------------------------------------
 -- Memory initialization state machine
 -------------------------------------------------------------------------------

 U_QDRII_PHY_INIT_SM : qdrii_phy_init_sm
   generic map(
     BURST_LENGTH => BURST_LENGTH,
     SIM_ONLY     => SIM_ONLY,
     CLK_FREQ     => CLK_FREQ
     )
   port map(
     clk0              => clk0,
     user_rst_0        => user_rst_0,
     dly_cal_done      => dly_cal_done,
     q_init_delay_done => q_init_delay_done,
     en_cal_done       => we_cal_done,
     dly_ready         => idly_ctrl_rdy,
     dly_cal_start     => dly_cal_start,
     we_cal_start      => we_cal_start,
     dummy_write       => dummy_write,
     dummy_read        => dummy_read_i,
     cal_done          => cal_done_i,
     init_cnt_done     => init_cnt_done_i
     );


  CAL_INST_36 : if(MEMORY_WIDTH = 36) generate
    CAL_INST_CQ : for cqi in 0 to CQ_WIDTH-1 generate
      ----------------------------------------------------------------------------
      -- Delay calibration module CQ instantiation for 36 bit component
      ----------------------------------------------------------------------------
      U_QDRII_PHY_DLY_CAL_SM_CQ : qdrii_phy_dly_cal_sm
        generic map(
          BURST_LENGTH => BURST_LENGTH,
          CQ_WIDTH     => CQ_WIDTH,
          DATA_WIDTH   => DATA_WIDTH,
          DEBUG_EN     => DEBUG_EN,
          Q_PER_CQ     => Q_PER_CQ,
          Q_PER_CQ_9   => Q_PER_CQ_9
          )
        port map(
          clk0              => clk0,
          user_rst_0        => user_rst_0,
          start_cal         => dly_cal_start,
          rd_data_rise      => rd_data_rise((((2*cqi)+1)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*2*cqi)),
          rd_data_fall      => rd_data_fall((((2*cqi)+1)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*2*cqi)),
          rd_en             => rd_cmd_in,
          we_cal_start      => we_cal_start,
          q_dly_rst         => q_cq_dly_rst(cqi),
          q_dly_ce          => q_cq_dly_ce(cqi),
          q_dly_inc         => q_cq_dly_inc(cqi),
          cq_dly_rst        => cq_dly_rst(cqi),
          cq_dly_ce         => cq_dly_ce(cqi),
          cq_dly_inc        => cq_dly_inc(cqi),
          dly_cal_done      => dly_cal_done_cq_inst(cqi),
          q_delay_done      => q_init_delay_done,
          q_init_delay_done => q_init_delay_done_cq_inst(cqi),
          rdfifo_we         => data_valid_cq_inst(cqi),
          we_cal_done       => we_cal_done_cq_inst(cqi),
          srl_count         => srl_count((((2*cqi)+1)*4)-1 downto (2*cqi*4)),
          -- Debug Signals
          dbg_idel_up_q_cq                => dbg_idel_up_q_cq_i,
          dbg_idel_down_q_cq              => dbg_idel_down_q_cq_i,
          dbg_idel_up_cq                  => dbg_idel_up_cq_i,
          dbg_idel_down_cq                => dbg_idel_down_cq_i,
          dbg_sel_idel_q_cq               => dbg_sel_idel_q_cq_i(cqi),
          dbg_sel_idel_cq                 => dbg_sel_idel_cq_i(cqi),
          dbg_q_init_delay_done_tap_count => dbg_q_cq_init_delay_done_tap_count(((cqi+1)*6)-1 downto (cqi*6)),
          dbg_cq_cal_tap_count            => dbg_cq_cal_tap_count(((cqi+1)*6)-1 downto (cqi*6))
          );
    end generate CAL_INST_CQ;

    CAL_INST_CQ_N : for cq_ni in 0 to CQ_WIDTH-1 generate
      ----------------------------------------------------------------------------
      -- Delay calibration module CQ# instantiation for 36 bit component
      ----------------------------------------------------------------------------
      U_QDRII_PHY_DLY_CAL_SM_CQ_N : qdrii_phy_dly_cal_sm
        generic map(
          BURST_LENGTH => BURST_LENGTH,
          CQ_WIDTH     => CQ_WIDTH,
          DATA_WIDTH   => DATA_WIDTH,
          DEBUG_EN     => DEBUG_EN,
          Q_PER_CQ     => Q_PER_CQ,
          Q_PER_CQ_9   => Q_PER_CQ_9
          )
        port map(
          clk0              => clk0,
          user_rst_0        => user_rst_0,
          start_cal         => dly_cal_start,
          rd_data_rise      => rd_data_rise((((2*cq_ni)+2)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*((2*cq_ni)+1))),
          rd_data_fall      => rd_data_fall((((2*cq_ni)+2)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*((2*cq_ni)+1))),
          rd_en             => rd_cmd_in,
          we_cal_start      => we_cal_start,
          q_dly_rst         => q_cq_n_dly_rst(cq_ni),
          q_dly_ce          => q_cq_n_dly_ce(cq_ni),
          q_dly_inc         => q_cq_n_dly_inc(cq_ni),
          cq_dly_rst        => cq_n_dly_rst(cq_ni),
          cq_dly_ce         => cq_n_dly_ce(cq_ni),
          cq_dly_inc        => cq_n_dly_inc(cq_ni),
          dly_cal_done      => dly_cal_done_cq_n_inst(cq_ni),
          q_delay_done      => q_init_delay_done,
          q_init_delay_done => q_init_delay_done_cq_n_inst(cq_ni),
          rdfifo_we         => data_valid_cq_n_inst(cq_ni),
          we_cal_done       => we_cal_done_cq_n_inst(cq_ni),
          srl_count         => srl_count(((((2*cq_ni)+1)+1)*4)-1 downto (((2*cq_ni)+1)*4)),
          -- Debug Signals
          dbg_idel_up_q_cq                => dbg_idel_up_q_cq_n_i,
          dbg_idel_down_q_cq              => dbg_idel_down_q_cq_n_i,
          dbg_idel_up_cq                  => dbg_idel_up_cq_n_i,
          dbg_idel_down_cq                => dbg_idel_down_cq_n_i,
          dbg_sel_idel_q_cq               => dbg_sel_idel_q_cq_n_i(cq_ni),
          dbg_sel_idel_cq                 => dbg_sel_idel_cq_n_i(cq_ni),
          dbg_q_init_delay_done_tap_count => dbg_q_cq_n_init_delay_done_tap_count(((cq_ni+1)*6)-1 downto (cq_ni*6)),
          dbg_cq_cal_tap_count            => dbg_cq_n_cal_tap_count(((cq_ni+1)*6)-1 downto (cq_ni*6))
          );
    end generate CAL_INST_CQ_N;
  end generate CAL_INST_36;

  CAL_INST_18_9 : if(MEMORY_WIDTH /= 36) generate
    CAL_INST_CQ : for cqi in 0 to CQ_WIDTH-1 generate
      ----------------------------------------------------------------------------
      -- Delay calibration module CQ instantiation for 18bit & 9bit component
      ----------------------------------------------------------------------------
      U_QDRII_PHY_DLY_CAL_SM_CQ : qdrii_phy_dly_cal_sm
        generic map(
          BURST_LENGTH => BURST_LENGTH,
          CQ_WIDTH     => CQ_WIDTH,
          DATA_WIDTH   => DATA_WIDTH,
          DEBUG_EN     => DEBUG_EN,
          Q_PER_CQ     => Q_PER_CQ,
          Q_PER_CQ_9   => Q_PER_CQ_9
          )
        port map(
          clk0              => clk0,
          user_rst_0        => user_rst_0,
          start_cal         => dly_cal_start,
          rd_data_rise      => rd_data_rise(((cqi+1)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*cqi)),
          rd_data_fall      => rd_data_fall(((cqi+1)*Q_PER_CQ)-1 downto
                                            (Q_PER_CQ*cqi)),
          rd_en             => rd_cmd_in,
          we_cal_start      => we_cal_start,
          q_dly_rst         => q_cq_dly_rst(cqi),
          q_dly_ce          => q_cq_dly_ce(cqi),
          q_dly_inc         => q_cq_dly_inc(cqi),
          cq_dly_rst        => cq_dly_rst(cqi),
          cq_dly_ce         => cq_dly_ce(cqi),
          cq_dly_inc        => cq_dly_inc(cqi),
          dly_cal_done      => dly_cal_done_cq_inst(cqi),
          q_delay_done      => q_init_delay_done,
          q_init_delay_done => q_init_delay_done_cq_inst(cqi),
          rdfifo_we         => data_valid_cq_inst(cqi),
          we_cal_done       => we_cal_done_cq_inst(cqi),
          srl_count         => srl_count(((cqi+1)*4)-1 downto cqi*4),
          -- Debug Signals
          dbg_idel_up_q_cq                => dbg_idel_up_q_cq_i,
          dbg_idel_down_q_cq              => dbg_idel_down_q_cq_i,
          dbg_idel_up_cq                  => dbg_idel_up_cq_i,
          dbg_idel_down_cq                => dbg_idel_down_cq_i,
          dbg_sel_idel_q_cq               => dbg_sel_idel_q_cq_i(cqi),
          dbg_sel_idel_cq                 => dbg_sel_idel_cq_i(cqi),
          dbg_q_init_delay_done_tap_count => dbg_q_cq_init_delay_done_tap_count(((cqi+1)*6)-1 downto (cqi*6)),
          dbg_cq_cal_tap_count            => dbg_cq_cal_tap_count(((cqi+1)*6)-1 downto (cqi*6))
          );
    end generate CAL_INST_CQ;
  end generate CAL_INST_18_9;

  U_QDRII_PHY_EN : qdrii_phy_en
    generic map (
      DATA_WIDTH   => DATA_WIDTH,
      CQ_WIDTH     => CQ_WIDTH,
      Q_PER_CQ     => Q_PER_CQ,
      STROBE_WIDTH => STROBE_WIDTH
      )
    port map(
        clk0              => clk0,
        user_rst_0        => user_rst_0,
        we_cal_done       => we_cal_done,
        rd_data_rise      => rd_data_rise,
        rd_data_fall      => rd_data_fall,
        we_in             => data_valid_inst(STROBE_WIDTH-1 downto 0),
        srl_count         => srl_count((STROBE_WIDTH*4)-1 downto 0),
        rd_data_rise_out  => rd_data_rise_out,
        rd_data_fall_out  => rd_data_fall_out,
        data_valid_out    => data_valid_out
        );

  -- synthesis translate_off
  process(init_cnt_done_i)
  begin
    if(user_rst_0 = '0') then
      if(init_cnt_done_i'event and init_cnt_done_i = '1')then
        report "INITIALIZATION PERIOD OF 200uSec IS COMPLETE at time " & time'image(now);
      end if;
    end if;
  end process;

  process(q_init_delay_done)
  begin
    if(user_rst_0 = '0') then
      if(q_init_delay_done'event and q_init_delay_done = '1')then
        report "FIRST STAGE CALIBRATION COMPLETE at time " & time'image(now);
      end if;
    end if;
  end process;

  process(dly_cal_done)
  begin
    if(user_rst_0 = '0') then
      if(dly_cal_done'event and dly_cal_done = '1')then
        report "SECOND STAGE CALIBRATION COMPLETE at time " & time'image(now);
      end if;
    end if;
  end process;

  process(we_cal_done)
  begin
    if(user_rst_0 = '0') then
      if(we_cal_done'event and we_cal_done = '1')then
        report "READ ENABLE CALIBRATION COMPLETE at time " & time'image(now);
       end if;
    end if;
  end process;

  -- synthesis translate_on

  -- Generate QDR_R_n logic

  rd_cmd_in <= '0' when ((rd_init_n = '0') or (dummy_read_i /= "00")) else '1';

  RD_INIT_FF1 : FDP
    port map(
      Q   => rd_init_delay_n_i,
      D   => rd_cmd_in,
      C   => clk270,
      PRE => user_rst_270
      );

  RD_INIT_FF2 : FDP
    port map(
      Q   => rd_init_delay2_n_i,
      D   => rd_init_delay_n_i,
      C   => clk180,
      PRE => user_rst_180
      );

  BL4_INST : if(BURST_LENGTH = 4) generate
  attribute syn_useioff of RD_INIT_FF3 : label is true;
  attribute IOB of RD_INIT_FF3 : label is "true";
  begin
    RD_INIT_FF3 : FDP
      port map(
        Q   => qdr_r_n_int,
        D   => rd_init_delay2_n_i,
        C   => clk180,
        PRE => user_rst_180
        );
  end generate;

  BL2_INST : if(BURST_LENGTH = 2) generate
  attribute syn_useioff of RD_INIT_FF4 : label is true;
  attribute IOB of RD_INIT_FF4 : label is "true";
  begin
    RD_INIT_FF3 : FDP
      port map(
        Q   => rd_init_delay3_n,
        D   => rd_init_delay2_n_i,
        C   => clk180,
        PRE => user_rst_180
        );

    RD_INIT_FF4 : FDP
      port map(
        Q   => qdr_r_n_int,
        D   => rd_init_delay3_n,
        C   => clk180,
        PRE => user_rst_180
        );
  end generate;


  rd_init_delay_n  <= rd_init_delay_n_i;
  rd_init_delay2_n <= rd_init_delay2_n_i;

  QDR_R_N_INST : OBUF
    port map(
      I => qdr_r_n_int,
      O => qdr_r_n
      );

end architecture arch_qdrii_phy_read;
