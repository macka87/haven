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
--  /   /         Filename           : qdrii_phy_dly_cal_sm.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Calibrates the IDELAY tap values for the QDR_Q and QDR_CQ inputs
--          to allow direct capture of the read data into the system clock
--          domain.
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use unisim.vcomponents.all;

entity qdrii_phy_dly_cal_sm is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4;
    CLK_PERIOD   : integer := 3333;
    CQ_WIDTH     : integer := 2;
    DATA_WIDTH   : integer := 72;
    DEBUG_EN     : integer := 0;
    Q_PER_CQ_9   : integer := 2;
    Q_PER_CQ     : integer := 18
    );
  port(
    clk0              : in  std_logic;
    user_rst_0        : in  std_logic;
    start_cal         : in  std_logic;
    rd_data_rise      : in  std_logic_vector(Q_PER_CQ-1 downto 0);
    rd_data_fall      : in  std_logic_vector(Q_PER_CQ-1 downto 0);
    q_delay_done      : in  std_logic;
    rd_en             : in  std_logic;
    we_cal_start      : in  std_logic;
    q_dly_rst         : out std_logic;
    q_dly_ce          : out std_logic;
    q_dly_inc         : out std_logic;
    cq_dly_rst        : out std_logic;
    cq_dly_ce         : out std_logic;
    cq_dly_inc        : out std_logic;
    dly_cal_done      : out std_logic;
    q_init_delay_done : out std_logic;
    rdfifo_we         : out std_logic;
    we_cal_done       : out std_logic;
    srl_count         : out std_logic_vector(3 downto 0);
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
end qdrii_phy_dly_cal_sm;

architecture arch_qdrii_phy_dly_cal_sm of qdrii_phy_dly_cal_sm is

  constant PATTERN_A : std_logic_vector(8 downto 0) := "111111111";
  constant PATTERN_B : std_logic_vector(8 downto 0) := "000000000";
  constant PATTERN_C : std_logic_vector(8 downto 0) := "101010101";
  constant PATTERN_D : std_logic_vector(8 downto 0) := "010101010";

  constant IDLE         : std_logic_vector(8 downto 0) := "000000001";  --01
  constant CQ_TAP_INC   : std_logic_vector(8 downto 0) := "000000010";  --02
  constant CQ_TAP_RST   : std_logic_vector(8 downto 0) := "000000100";  --04
  constant Q_TAP_INC    : std_logic_vector(8 downto 0) := "000001000";  --08
  constant Q_TAP_RST    : std_logic_vector(8 downto 0) := "000010000";  --10
  constant CQ_Q_TAP_INC : std_logic_vector(8 downto 0) := "000100000";  --20
  constant CQ_Q_TAP_DEC : std_logic_vector(8 downto 0) := "001000000";  --40
  constant TAP_WAIT     : std_logic_vector(8 downto 0) := "010000000";  --80
  constant DEBUG_ST     : std_logic_vector(8 downto 0) := "100000000";  --100

  constant COMP_1      : std_logic_vector(2 downto 0) := "001";  --001
  constant COMP_2      : std_logic_vector(2 downto 0) := "010";  --002
  constant CAL_DONE_ST : std_logic_vector(2 downto 0) := "100";  --004

  constant Q_ERROR_CHECK : std_logic_vector(5 downto 0) := "000001";  --001
  constant Q_ERROR_1     : std_logic_vector(5 downto 0) := "000010";  --002
  constant Q_ERROR_2     : std_logic_vector(5 downto 0) := "000100";  --004
  constant Q_ERROR_1_2   : std_logic_vector(5 downto 0) := "001000";  --008
  constant Q_ERROR_2_2   : std_logic_vector(5 downto 0) := "010000";  --010
  constant Q_ERROR_ST    : std_logic_vector(5 downto 0) := "100000";  --020

--  constant half_period_taps    : integer := (1000000/(CLK_FREQ*150));
  constant half_period_taps : integer := CLK_PERIOD/150;

  signal max_window            : unsigned(5 downto 0);
  signal tap_wait_cnt          : unsigned(2 downto 0);
  signal q_tap_range           : unsigned(5 downto 0);
  signal cq_tap_cnt            : unsigned(5 downto 0);
  signal q_tap_cnt             : unsigned(5 downto 0);
  signal cq_tap_range          : unsigned(5 downto 0);
  signal cal1_taprange         : unsigned(5 downto 0);
  signal cq_hold_range         : unsigned(5 downto 0);
  signal cq_setup_range        : unsigned(5 downto 0);
  signal cq_tap_range_center   : unsigned(5 downto 0);
  signal cal1_tapcenter        : unsigned(5 downto 0);
  signal cq_tap_range_center_w : unsigned(5 downto 0);
  signal insuff_window_taps    : unsigned(5 downto 0);
  signal cq_final_tap_cnt      : unsigned(5 downto 0);
  signal cq_window_range_sh    : unsigned(5 downto 0);
  signal cq_window_range_hs    : unsigned(5 downto 0);
  signal tap_inc_val           : unsigned(5 downto 0);
  signal tap_inc_range         : unsigned(5 downto 0);
  signal rden_cnt_clk0         : unsigned(3 downto 0);
  signal rd_stb_cnt            : unsigned(1 downto 0);
  signal we_cal_cnt            : unsigned(2 downto 0);

  signal rd_data_rise_r           : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal rd_data_fall_r           : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal cal1_chk                 : std_logic;
  signal cal2_chk_1               : std_logic;
  signal cal2_chk_2               : std_logic;
  signal next_state               : std_logic_vector(8 downto 0);
  signal q_error_state            : std_logic_vector(5 downto 0);
  signal cal_begin                : std_logic;
  signal first_edge_detect        : std_logic;
  signal first_edge_detect_r      : std_logic;
  signal second_edge_detect       : std_logic;
  signal second_edge_detect_r     : std_logic;
  signal cq_q_detect_done         : std_logic;
  signal cq_q_detect_done_r       : std_logic;
  signal cq_q_detect_done_2r      : std_logic;
  signal dvw_detect_done          : std_logic;
  signal dvw_detect_done_r        : std_logic;
  signal insuff_window_detect     : std_logic;
  signal insuff_window_detect_r   : std_logic;
  signal cq_cal_done              : std_logic;
  signal clk0_cal                 : std_logic;
  signal end_of_taps              : std_logic;
  signal tap_wait_en              : std_logic;
  signal start_cal_r              : std_logic;
  signal start_cal_2r             : std_logic;
  signal start_cal_3r             : std_logic;
  signal start_cal_4r             : std_logic;
  signal start_cal_5r             : std_logic;
  signal start_cal_6r             : std_logic;
  signal q_error                  : std_logic;
  signal q1_error                 : std_logic;
  signal q2_error                 : std_logic;
  signal q_initdelay_inc_done     : std_logic;
  signal q_initdelay_inc_done_r   : std_logic;
  signal q_initdelay_dec_done     : std_logic;
  signal q_initdelay_dec_done_r   : std_logic;
  signal q_initdelay_done         : std_logic;
  signal cal1_error               : std_logic;
  signal q_delay_done_r           : std_logic;
  signal q_delay_done_2r          : std_logic;
  signal q_delay_done_3r          : std_logic;
  signal q_delay_done_4r          : std_logic;
  signal q_delay_done_5r          : std_logic;
  signal q_delay_done_6r          : std_logic;
  signal q_delay_done_7r          : std_logic;
  signal q_delay_done_8r          : std_logic;
  signal q_delay_done_9r          : std_logic;
  signal q_delay_done_10r         : std_logic;
  signal q_delay_done_11r         : std_logic;
  signal q_delay_done_12r         : std_logic;
  signal q_delay_done_13r         : std_logic;
  signal q_delay_done_14r         : std_logic;
  signal q_delay_done_15r         : std_logic;
  signal q_delay_done_16r         : std_logic;
  signal q_delay_done_17r         : std_logic;
  signal q_delay_done_18r         : std_logic;
  signal q_delay_done_19r         : std_logic;
  signal q_delay_done_20r         : std_logic;
  signal q_delay_done_21r         : std_logic;
  signal q_delay_done_22r         : std_logic;
  signal q_delay_done_23r         : std_logic;
  signal q_delay_done_24r         : std_logic;
  signal q_delay_done_25r         : std_logic;
  signal q_delay_done_26r         : std_logic;
  signal q_delay_done_27r         : std_logic;
  signal q_delay_done_28r         : std_logic;
  signal q_delay_done_29r         : std_logic;
  signal q_delay_done_30r         : std_logic;
  signal q_delay_done_31r         : std_logic;
  signal q_delay_done_32r         : std_logic;
  signal q_insuff_initdelay       : std_logic;
  signal q_initdelay_dec_done_2r  : std_logic;
  signal q_detect_chk             : std_logic;
  signal cnt_rst                  : std_logic;
  signal insuff_window_detect_p   : std_logic;
  signal q_dly_inc_i              : std_logic;
  signal q_dly_ce_i               : std_logic;
  signal q_dly_rst_i              : std_logic;
  signal cq_dly_ce_i              : std_logic;
  signal cq_dly_inc_i             : std_logic;
  signal cq_dly_rst_i             : std_logic;
  signal cq_initdelay_inc_done    : std_logic;
  signal cq_rst_done              : std_logic;
  signal q_rst_done               : std_logic;
  signal pat_a                    : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal pat_b                    : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal pat_c                    : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal pat_d                    : std_logic_vector(Q_PER_CQ-1 downto 0);
  signal cq_initdelay_inc_done_r  : std_logic;
  signal q_init_delay_done_r      : std_logic;
  signal q_initdelay_inc_done_2r  : std_logic;
  signal cq_initdelay_inc_done_2r : std_logic;
  signal q_init_delay_done_2r     : std_logic;
  signal q_initdelay_done_p       : std_logic;
  signal cq_initdelay_done_p      : std_logic;
  signal q_inc_delay_done_p       : std_logic;
  signal rd_cmd                   : std_logic;
  signal comp_cs                  : std_logic_vector(2 downto 0);
  signal write_cal_start          : std_logic;
  signal rden_srl_clk0            : std_logic;
  signal we_cal_done_i            : std_logic;
  signal rdfifo_we_i              : std_logic;
  signal we_cal_done_r            : std_logic;
  signal rd_en_i                  : std_logic;
  signal cq_inc_flag              : std_logic;
  signal q_inc_flag               : std_logic;
  signal user_rst_r               : std_logic;
  signal user_rst_r1              : std_logic;
  signal low_freq_min_window      : unsigned(5 downto 0);

begin

  -- Low frequency window for second stage: For clk_period > 4000ps
  -- if CQ/Q and CLK0 are less than 20 taps apart, insuff_window_detect is asserted.
  -- Then, for frequencies with half period more than 30 taps, CQ and Q are both delayed by a fixed 30 taps.
  -- Else they are both delayed by half period worth of taps so that they are both aligned to the next fpga clock edge
  -- if CQ/Q and CLK0 are more than 40 taps apart, they are then delayed such that CQ/Q are atleast (cq_tap_range/2) taps away from clk0

  low_freq_min_window <= "011110" when (half_period_taps > 30) else
                         TO_UNSIGNED(half_period_taps,6);

  dbg_q_init_delay_done_tap_count <= std_logic_vector(q_tap_cnt);
  dbg_cq_cal_tap_count            <= std_logic_vector(cq_tap_cnt);

  q_dly_inc  <= q_dly_inc_i;
  q_dly_ce   <= q_dly_ce_i;
  q_dly_rst  <= q_dly_rst_i;
  cq_dly_ce  <= cq_dly_ce_i;
  cq_dly_inc <= cq_dly_inc_i;
  cq_dly_rst <= cq_dly_rst_i;

--  max_window <= "001111" when CLK_FREQ > 250 else
--                "010100";

  max_window <= "010100" when CLK_PERIOD > 4000 else
                "001111";

  ASGN : for i in 0 to Q_PER_CQ_9-1 generate
    pat_a(((i+1)*9)-1 downto (9*i)) <= PATTERN_A;
    pat_b(((i+1)*9)-1 downto (9*i)) <= PATTERN_B;
    pat_c(((i+1)*9)-1 downto (9*i)) <= PATTERN_C;
    pat_d(((i+1)*9)-1 downto (9*i)) <= PATTERN_D;
  end generate ASGN;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      user_rst_r1 <= user_rst_0;
      user_rst_r  <= user_rst_r1;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        rd_data_rise_r <= (others => '0');
        rd_data_fall_r <= (others => '0');
      else
        rd_data_rise_r <= rd_data_rise;
        rd_data_fall_r <= rd_data_fall;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if ((rd_data_rise_r = pat_a) and (rd_data_fall_r = pat_b)) then
        cal1_chk <= '1';
      else
        cal1_chk <= '0';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(q_initdelay_inc_done = '1') then
        cal1_error   <= '0';
      elsif(tap_wait_cnt = "101") then
        if(cal1_chk = '1') then
          cal1_error <= '0';
        else
          cal1_error <= '1';
        end if;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cal2_chk_1 <= '0';
      elsif ((rd_data_rise_r = pat_a) and (rd_data_fall_r = pat_b)) then
        cal2_chk_1 <= '1';
      else
        cal2_chk_1 <= '0';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cal2_chk_2 <= '0';
      elsif ((rd_data_rise_r = pat_c) and (rd_data_fall_r = pat_d)) then
        cal2_chk_2 <= '1';
      else
        cal2_chk_2 <= '0';
      end if;
    end if;
  end process;

  dly_cal_done      <= cq_cal_done;
  q_init_delay_done <= q_initdelay_done;

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      if (user_rst_r = '1') then
        q_error       <= '0';
        q_error_state <= Q_ERROR_CHECK;
      else
        case(q_error_state) is
          when Q_ERROR_CHECK =>
            if (q_delay_done_32r = '1' and tap_wait_cnt = "101") then
              if (cal2_chk_1 = '1') then
                q_error       <= '0';
                q_error_state <= Q_ERROR_1;
              elsif (cal2_chk_2 = '1') then
                q_error       <= '0';
                q_error_state <= Q_ERROR_2;
              else
                q_error       <= '1';
                q_error_state <= Q_ERROR_ST;
              end if;
            else
              q_error       <= q_error;
              q_error_state <= Q_ERROR_CHECK;
            end if;

          when Q_ERROR_1 =>
            if (cal2_chk_2 = '1') then
              q_error <= '0';
              q_error_state <= Q_ERROR_1_2;
            else
              q_error <= '1';
              q_error_state <= Q_ERROR_ST;
            end if;

          when Q_ERROR_1_2 =>
            if (cal2_chk_1 = '1') then
              q_error <= '0';
              q_error_state <= Q_ERROR_1;
            else
              q_error <= '1';
              q_error_state <= Q_ERROR_ST;
            end if;

          when Q_ERROR_2 =>
            if (cal2_chk_1 = '1') then
              q_error <= '0';
              q_error_state <= Q_ERROR_2_2;
            else
              q_error <= '1';
              q_error_state <= Q_ERROR_ST;
            end if;


          when Q_ERROR_2_2 =>
            if (cal2_chk_2 = '1') then
              q_error <= '0';
              q_error_state <= Q_ERROR_2;
            else
              q_error <= '1';
              q_error_state <= Q_ERROR_ST;
            end if;

          when Q_ERROR_ST =>
            q_error       <= '1';
            q_error_state <= Q_ERROR_CHECK;

          when others =>
            q_error       <= '0';
            q_error_state <= Q_ERROR_CHECK;

        end case;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        start_cal_r  <= '0';
        start_cal_2r <= '0';
        start_cal_3r <= '0';
        start_cal_4r <= '0';
        start_cal_5r <= '0';
        start_cal_6r <= '0';
      else
        start_cal_r  <= start_cal;
        start_cal_2r <= start_cal_r;
        start_cal_3r <= start_cal_2r;
        start_cal_4r <= start_cal_3r;
        start_cal_5r <= start_cal_4r;
        start_cal_6r <= start_cal_5r;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_delay_done_r   <= '0';
        q_delay_done_2r  <= '0';
        q_delay_done_3r  <= '0';
        q_delay_done_4r  <= '0';
        q_delay_done_5r  <= '0';
        q_delay_done_6r  <= '0';
        q_delay_done_7r  <= '0';
        q_delay_done_8r  <= '0';
        q_delay_done_9r  <= '0';
        q_delay_done_10r <= '0';
        q_delay_done_11r <= '0';
        q_delay_done_12r <= '0';
        q_delay_done_13r <= '0';
        q_delay_done_14r <= '0';
        q_delay_done_15r <= '0';
        q_delay_done_16r <= '0';
        q_delay_done_17r <= '0';
        q_delay_done_18r <= '0';
        q_delay_done_19r <= '0';
        q_delay_done_20r <= '0';
        q_delay_done_21r <= '0';
        q_delay_done_22r <= '0';
        q_delay_done_23r <= '0';
        q_delay_done_24r <= '0';
        q_delay_done_25r <= '0';
        q_delay_done_26r <= '0';
        q_delay_done_27r <= '0';
        q_delay_done_28r <= '0';
        q_delay_done_29r <= '0';
        q_delay_done_30r <= '0';
        q_delay_done_31r <= '0';
        q_delay_done_32r <= '0';
      else
        q_delay_done_r   <= q_delay_done;
        q_delay_done_2r  <= q_delay_done_r;
        q_delay_done_3r  <= q_delay_done_2r;
        q_delay_done_4r  <= q_delay_done_3r;
        q_delay_done_5r  <= q_delay_done_4r;
        q_delay_done_6r  <= q_delay_done_5r;
        q_delay_done_7r  <= q_delay_done_6r;
        q_delay_done_8r  <= q_delay_done_7r;
        q_delay_done_9r  <= q_delay_done_8r;
        q_delay_done_10r <= q_delay_done_9r;
        q_delay_done_11r <= q_delay_done_10r;
        q_delay_done_12r <= q_delay_done_11r;
        q_delay_done_13r <= q_delay_done_12r;
        q_delay_done_14r <= q_delay_done_13r;
        q_delay_done_15r <= q_delay_done_14r;
        q_delay_done_16r <= q_delay_done_15r;
        q_delay_done_17r <= q_delay_done_16r;
        q_delay_done_18r <= q_delay_done_17r;
        q_delay_done_19r <= q_delay_done_18r;
        q_delay_done_20r <= q_delay_done_19r;
        q_delay_done_21r <= q_delay_done_20r;
        q_delay_done_22r <= q_delay_done_21r;
        q_delay_done_23r <= q_delay_done_22r;
        q_delay_done_24r <= q_delay_done_23r;
        q_delay_done_25r <= q_delay_done_24r;
        q_delay_done_26r <= q_delay_done_25r;
        q_delay_done_27r <= q_delay_done_26r;
        q_delay_done_28r <= q_delay_done_27r;
        q_delay_done_29r <= q_delay_done_28r;
        q_delay_done_30r <= q_delay_done_29r;
        q_delay_done_31r <= q_delay_done_30r;
        q_delay_done_32r <= q_delay_done_31r;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cal_begin <= '0';
      elsif((start_cal_5r = '1') and (start_cal_6r = '0')) then
        cal_begin <= '1';
      elsif(q_dly_inc_i = '1') then
        cal_begin <= '0';
      end if;
    end if;
  end process;


--------------------------------------------------------------------------------
-- 1. CQ-Q calibration
--
-- This stage is required since cq is delayed by an amount equal to the bufio
-- delay with respect to the data. This might move CQ towards the end of the
-- data window at higher frequencies. This stage of calibration helps to align
-- data within the CQ window. In this stage, a static data pattern of 1s and 0s
-- are written as rise and fall data respectively. This pattern also helps to
-- eliminate any metastability arising due to the phase alignment of the
-- data output from the ISERDES and the FPGA clock.
-- The stages of this calibration are as follows:
-- 1. Increment the cq taps to determine the hold data window.
-- 2. Reset the CQ taps once the end of window is reached or sufficient window
--    not detected.
-- 3. Increment Q taps to determine the set up window.
-- 4. Reset the q taps.
-- 5. If the hold window detected is greater than the set up window, then no
--    tap increments needed. If the hold window is less than the setup window,
--    data taps are incremented so that CQ is in the center of the
--    data valid window.
--
-- 2. CQ-Q to FPGA clk calibration
--
-- This stage helps to determine the relationship between cq/q with respect to
-- the fpga clk.
-- 1. CQ and Q are incremented and the window detected with respect to the
--    FPGA clk. If there is insufficient window , CQ/Q are both incremented
--    so that they can be aligned to the next rising edge of the FPGA clk.
-- 2. Once sufficient window is detected, CQ and Q are decremented such that
--    they are atleast half the clock period away from the FPGA clock in case of
--    frequencies lower than or equal to 250 MHz and atleast 20 taps away from
--    the FPGA clock for frequencies higher than 250 MHz.
--------------------------------------------------------------------------------

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      if((user_rst_r = '1') or (start_cal = '0')) then
        cq_dly_inc_i <= '0';
        cq_dly_ce_i  <= '0';
        cq_dly_rst_i <= '1';
        q_dly_inc_i  <= '0';
        q_dly_ce_i   <= '0';
        q_dly_rst_i  <= '1';
        tap_wait_en  <= '0';
        next_state   <= IDLE;
      else
        case(next_state) is
          when IDLE =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '0';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '0';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '0';

--            if((cal_begin = '1') and (cq_initdelay_inc_done = '0')) then
            if(((cal_begin = '1') and (cq_initdelay_inc_done = '0')) or
               ((q_rst_done = '1') and (cq_inc_flag = '1') and
                                       (q_initdelay_done = '0'))) then
              next_state <= CQ_TAP_INC;
            elsif((cq_initdelay_inc_done_r = '1') and (cq_rst_done = '0')) then
              next_state <= CQ_TAP_RST;
            elsif(((cq_rst_done = '1') and (q_initdelay_inc_done = '0')) or
--                  ((q_rst_done = '1') and (q_initdelay_done = '0'))) then
                  ((q_rst_done = '1') and (q_initdelay_done = '0') and
                                          (q_inc_flag = '1'))) then
              next_state <= Q_TAP_INC;
            elsif((q_initdelay_inc_done_r = '1') and (q_rst_done = '0')) then
              next_state <= Q_TAP_RST;
            elsif((q_delay_done_32r = '1') and (cq_q_detect_done = '0')) then
              next_state <= CQ_Q_TAP_INC;
            elsif((cq_q_detect_done_2r = '1') and (cq_cal_done = '0')) then
              next_state <= CQ_Q_TAP_DEC;
            elsif((we_cal_done_i = '1') and (DEBUG_EN = 1)) then
              if(dbg_sel_idel_q_cq = '1') then
                q_dly_inc_i <= dbg_idel_up_q_cq;
                q_dly_ce_i  <= dbg_idel_up_q_cq or dbg_idel_down_q_cq;
              else
                q_dly_ce_i  <= '0';
              end if;

              if(dbg_sel_idel_cq = '1') then
                cq_dly_inc_i <= dbg_idel_up_cq;
                cq_dly_ce_i  <= dbg_idel_up_cq or dbg_idel_down_cq;
              else
                cq_dly_ce_i  <= '0';
              end if;
              next_state <= DEBUG_ST;
            else
              next_state <= IDLE;
            end if;

          when CQ_TAP_INC =>
            cq_dly_inc_i <= '1';
            cq_dly_ce_i  <= '1';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '0';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when CQ_TAP_RST =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '0';
            cq_dly_rst_i <= '1';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '0';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when Q_TAP_INC =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '0';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '1';
            q_dly_ce_i   <= '1';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when Q_TAP_RST =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '0';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '0';
            q_dly_rst_i  <= '1';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when CQ_Q_TAP_INC =>
            cq_dly_inc_i <= '1';
            cq_dly_ce_i  <= '1';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '1';
            q_dly_ce_i   <= '1';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when CQ_Q_TAP_DEC =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '1';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '1';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '1';
            next_state   <= TAP_WAIT;

          when TAP_WAIT =>
            cq_dly_inc_i <= '0';
            cq_dly_ce_i  <= '0';
            cq_dly_rst_i <= '0';
            q_dly_inc_i  <= '0';
            q_dly_ce_i   <= '0';
            q_dly_rst_i  <= '0';
            tap_wait_en  <= '0';

            if (tap_wait_cnt = "111") then
              next_state <= IDLE;
            else
              next_state <= TAP_WAIT;
            end if;

          when DEBUG_ST =>
            cq_dly_inc_i  <= '0';
            cq_dly_ce_i   <= '0';
            cq_dly_rst_i  <= '0';
            q_dly_inc_i   <= '0';
            q_dly_ce_i    <= '0';
            q_dly_rst_i   <= '0';
            tap_wait_en   <= '1';

            if(dbg_sel_idel_q_cq = '1') then
              q_dly_inc_i <= dbg_idel_up_q_cq;
              q_dly_ce_i  <= dbg_idel_up_q_cq or dbg_idel_down_q_cq;
            else
              q_dly_ce_i  <= '0';
            end if;

            if(dbg_sel_idel_cq = '1') then
              cq_dly_inc_i <= dbg_idel_up_cq;
              cq_dly_ce_i  <= dbg_idel_up_cq or dbg_idel_down_cq;
            else
              cq_dly_ce_i  <= '0';
            end if;

            if((dbg_sel_idel_q_cq = '0') and (dbg_sel_idel_cq = '0')) then
              next_state <= IDLE;
            else
              next_state <= DEBUG_ST;
            end if;

          when others =>
            next_state <= IDLE;
        end case;
      end if;
    end if;
  end process;

  cnt_rst <= user_rst_r or insuff_window_detect_p or q_initdelay_done_p or
             cq_initdelay_done_p or q_inc_delay_done_p;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        first_edge_detect <= '0';
      elsif(((q_error = '0') and (cal1_error = '0')) and
            (tap_wait_cnt = "111")) then
        first_edge_detect <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        second_edge_detect <= '0';
      elsif((first_edge_detect = '1') and ((q_error = '1') or (cal1_error = '1')
                                           or (end_of_taps = '1'))) then
        second_edge_detect <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        first_edge_detect_r  <= '0';
        second_edge_detect_r <= '0';
      else
        first_edge_detect_r  <= first_edge_detect;
        second_edge_detect_r <= second_edge_detect;
      end if;
    end if;
  end process;

  q_detect_chk <= '1' when ((q_rst_done = '1') and (q_delay_done_32r = '0')) else
                  '0';

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        dvw_detect_done <= '0';
      elsif((second_edge_detect_r = '1') and (insuff_window_detect = '0')
            and (q_detect_chk = '0')) then
        dvw_detect_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        dvw_detect_done_r <= '0';
      else
        dvw_detect_done_r <= dvw_detect_done;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if((user_rst_r = '1') or (cq_dly_rst_i = '1')) then
        cq_tap_cnt <= (others => '0');
      elsif((cq_dly_ce_i = '1') and (cq_dly_inc_i = '1')) then
        cq_tap_cnt <= cq_tap_cnt + 1;
      elsif((cq_dly_ce_i = '1') and (cq_dly_inc_i = '0')) then
        cq_tap_cnt <= cq_tap_cnt - 1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if((user_rst_r = '1') or (q_dly_rst_i = '1')) then
        q_tap_cnt <= (others => '0');
      elsif((q_dly_ce_i = '1') and (q_dly_inc_i = '1')) then
        q_tap_cnt <= q_tap_cnt + 1;
      elsif((q_dly_ce_i = '1') and (q_dly_inc_i = '0')) then
        q_tap_cnt <= q_tap_cnt - 1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        tap_wait_cnt <= "000";
      elsif((tap_wait_cnt /= "000") or (tap_wait_en = '1')) then
        tap_wait_cnt <= tap_wait_cnt + 1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        cq_tap_range <= (others => '0');
      elsif((cq_dly_inc_i = '1') and (first_edge_detect = '1')) then
        cq_tap_range <= cq_tap_range + 1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        q_tap_range <= (others => '0');
      elsif((q_dly_inc_i = '1') and (first_edge_detect = '1')) then
        q_tap_range <= q_tap_range + 1;
      end if;
    end if;
  end process;

--------------------------------------------------------------------------------
-- 1st stage calibration registers
--------------------------------------------------------------------------------

-- either end of window reached or no window detected
  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_initdelay_inc_done <= '0';
      elsif (((cq_initdelay_inc_done = '0') and (dvw_detect_done = '1') and
              (dvw_detect_done_r = '0')) or ((cq_tap_cnt = "000101") and
                                             (first_edge_detect = '0'))) then
        cq_initdelay_inc_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_initdelay_inc_done <= '0';
      elsif ((cq_initdelay_inc_done = '1') and (q_initdelay_inc_done = '0') and
             (dvw_detect_done = '1') and (dvw_detect_done_r = '0') and
--             (q_tap_range > "000111")) then
             (q_tap_range >= "000101")) then
        q_initdelay_inc_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_rst_done <= '0';
      elsif ((cq_initdelay_inc_done = '1') and (cq_dly_rst_i = '1')) then
        cq_rst_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_rst_done <= '0';
      elsif ((q_initdelay_inc_done = '1') and (q_dly_rst_i = '1')) then
        q_rst_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_hold_range <= (others => '0');
      elsif ((cq_initdelay_inc_done = '0') and (cq_dly_inc_i = '1') and
             (first_edge_detect = '1') ) then
        cq_hold_range <= cq_hold_range + 1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_setup_range <= (others => '0');
      elsif ((q_initdelay_inc_done = '0') and (q_dly_inc_i = '1') and
             (first_edge_detect = '1') ) then
        cq_setup_range <= cq_setup_range +1;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_initdelay_inc_done_r   <= '0';
        cq_initdelay_inc_done_r  <= '0';
        q_init_delay_done_r      <= '0';
        q_initdelay_inc_done_2r  <= '0';
        cq_initdelay_inc_done_2r <= '0';
        q_init_delay_done_2r     <= '0';
      else
        q_initdelay_inc_done_r   <= q_initdelay_inc_done;
        cq_initdelay_inc_done_r  <= cq_initdelay_inc_done;
        q_init_delay_done_r      <= q_initdelay_done;
        q_initdelay_inc_done_2r  <= q_initdelay_inc_done_r;
        cq_initdelay_inc_done_2r <= cq_initdelay_inc_done_r;
        q_init_delay_done_2r     <= q_init_delay_done_r;
      end if;
    end if;
  end process;


  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_initdelay_done_p <= '0';
      elsif ((q_initdelay_inc_done_r = '1') and (q_initdelay_inc_done_2r = '0')) then
        q_initdelay_done_p <= '1';
      elsif (q_delay_done_30r = '1') then
        q_initdelay_done_p <= '0';
      end if;
    end if;
  end process;



-- q_initdelay_done_p  <= '1' when ((q_initdelay_inc_done_r = '1') and
--                                  (q_initdelay_inc_done_2r = '0')) else '0';
  cq_initdelay_done_p <= '1' when ((cq_initdelay_inc_done_r = '1') and
                                   (cq_initdelay_inc_done_2r = '0')) else '0';
  q_inc_delay_done_p  <= '1' when ((q_init_delay_done_r = '1') and
                                   (q_init_delay_done_2r = '0')) else '0';

  cq_window_range_sh <= (cq_setup_range - cq_hold_range);
  cq_window_range_hs <= (cq_hold_range - cq_setup_range);

--  q_tap_inc_val <= ('0' & cq_window_range(5 downto 1)) when
--                   ((q_initdelay_inc_done_r = '1') and
--                    (cq_setup_range > cq_hold_range)) else
--                   "000000";

  tap_inc_val <= ('0' & cq_window_range_sh(5 downto 1)) when
                  ((q_initdelay_inc_done_r = '1') and
                   (cq_setup_range > cq_hold_range)) else
                 ('0' & cq_window_range_hs(5 downto 1));

  cq_inc_flag <= '1' when ((q_initdelay_inc_done = '1') and
                           (cq_hold_range > cq_setup_range)) else
                 '0';

  q_inc_flag <= '1' when ((q_initdelay_inc_done = '1') and
                          (cq_setup_range >= cq_hold_range)) else
                '0';

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        tap_inc_range <= (others => '0');
      else
        tap_inc_range <= tap_inc_val;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        q_initdelay_done <= '0';
      elsif ((q_rst_done = '1') and (q_initdelay_done = '0') and
             (((cq_inc_flag = '1') and (cq_tap_cnt = tap_inc_range)) or
              ((q_inc_flag = '1') and (q_tap_cnt = tap_inc_range)))) then
        q_initdelay_done <= '1';
      end if;
    end if;
  end process;

--------------------------------------------------------------------------------
-- 2nd stage calibration registers
--------------------------------------------------------------------------------

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_q_detect_done <= '0';
      elsif((q_delay_done_32r = '1') and (dvw_detect_done = '1') and
            (dvw_detect_done_r = '0')) then
        cq_q_detect_done <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_q_detect_done_r  <= '0';
        cq_q_detect_done_2r <= '0';
      else
        cq_q_detect_done_r  <= cq_q_detect_done;
        cq_q_detect_done_2r <= cq_q_detect_done_r;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        insuff_window_detect <= '0';
      elsif((q_delay_done_32r = '1') and (second_edge_detect = '1') and
            (cq_tap_range < max_window)) then
        insuff_window_detect <= '1';
      elsif((insuff_window_detect = '1') and (first_edge_detect_r = '1')) then
        insuff_window_detect <= '0';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        insuff_window_detect_r  <= '0';
      else
        insuff_window_detect_r  <= insuff_window_detect;
      end if;
    end if;
  end process;

  insuff_window_detect_p <= '1' when ((insuff_window_detect = '1') and
                                      (insuff_window_detect_r = '0')) else
                            '0';

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        insuff_window_taps <= (others => '0');
      elsif ((insuff_window_detect = '1') and (insuff_window_detect_r = '0'))then
         if (cq_inc_flag = '1') then
            insuff_window_taps <= q_tap_cnt;
         else
            insuff_window_taps <= cq_tap_cnt;
         end if;
      end if;
    end if;
  end process;

  cq_tap_range_center_w <= "000000" when (cq_tap_range < max_window) else
--                           low_freq_min_window when ((cq_tap_range < (2 * max_window)) and (CLK_FREQ < 250) and (insuff_window_taps > 0) ) else
                           low_freq_min_window when ((cq_tap_range < (2 * max_window)) and (CLK_PERIOD > 4000) and (insuff_window_taps > 0) ) else
                           (cq_tap_range - max_window) when (cq_tap_range < 2 * max_window) else
                           ('0' & cq_tap_range(5 downto 1));

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_tap_range_center <= (others => '0');
        cq_final_tap_cnt    <= (others => '0');
      else
        cq_tap_range_center <= cq_tap_range_center_w;
        cq_final_tap_cnt    <= insuff_window_taps + cq_tap_range_center;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(cnt_rst = '1') then
        end_of_taps <= '0';
      elsif( (cq_tap_cnt = "111010") or (q_tap_cnt = "111010"))then
        end_of_taps <= '1';
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        cq_cal_done <= '0';
      elsif(((cq_inc_flag = '1' and q_tap_cnt = cq_final_tap_cnt) or (q_inc_flag = '1' and cq_tap_cnt = cq_final_tap_cnt)) and (cq_q_detect_done = '1')) then
        cq_cal_done <= '1';
      end if;
    end if;
  end process;

--------------------------------------------------------------------------------
-- Third stage calibration statemachine.
-- Intermittent reads are issued to the same address. This stage of calibration
-- is used to align the read valid signal to the read data. The read valid
-- signal is generated from the read command by registering the command using a
-- shift register using SRL16. 'rden_cnt_clk0' is used to determine the number
-- of stages the read command needed to be registered to align with the read
-- data.
--------------------------------------------------------------------------------
  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        we_cal_done_i <= '0';
        comp_cs       <= COMP_1;
      else
        case(comp_cs) is
          when COMP_1 =>
            if((rdfifo_we_i = '1') and (write_cal_start = '1')) then
              if (cal2_chk_1 = '1') then
                we_cal_done_i <= '0';
                comp_cs       <= COMP_2;
              else
                we_cal_done_i <= '0';
                comp_cs       <= COMP_1;
              end if;
            else
              we_cal_done_i <= '0';
              comp_cs       <= COMP_1;
            end if;

          when COMP_2 =>
            if (cal2_chk_2 = '1') then
              we_cal_done_i <= '1';
              comp_cs       <= CAL_DONE_ST;
            else
              we_cal_done_i <= '0';
              comp_cs       <= COMP_1;
            end if;

          when CAL_DONE_ST =>
            we_cal_done_i <= '1';
            comp_cs       <= CAL_DONE_ST;

          when others =>
            we_cal_done_i <= '0';
            comp_cs       <= COMP_1;
        end case;
      end if;
    end if;
  end process;

  we_cal_done <= we_cal_done_i;

  BL4_INST : if(BURST_LENGTH = 4) generate
  -- For BL4 design, when a single read command is issued, 4 bursts of data is
  -- received. The same read command is expanded for two clock cycles and
  -- then the comparision of read data with pattern data is done in this
  -- particular two clock command window. Until the read data is matched with
  -- the pattern data, the two clock command window is shifted using SRL.
    process (clk0)
    begin
      if(rising_edge(clk0)) then
        if (user_rst_r = '1') then
          rd_stb_cnt <= "00";
        elsif (rd_en = '0') then
          rd_stb_cnt <= "10";
        elsif (rd_stb_cnt /= "00") then
          rd_stb_cnt <= rd_stb_cnt - 1;
        else
          rd_stb_cnt <= rd_stb_cnt;
        end if;
      end if;
    end process;

    process (clk0)
    begin
      if(rising_edge(clk0)) then
        if(user_rst_r = '1') then
          rd_cmd <= '0';
        elsif(rd_stb_cnt /= "00") then
          rd_cmd <= '1';
        else
          rd_cmd <= '0';
        end if;
      end if;
    end process;
  end generate;

  BL2_INST : if(BURST_LENGTH = 2) generate
  -- For BL2 design, when two consecutive read commands are issued, 4 bursts
  -- of data is received. The read data is compared with pattern data in this
  -- particular two clock command window. Until the read data is matched with
  -- the pattern data, the two clock command window is shifted using SRL.

    rd_stb_cnt <="00";

    process(clk0)
    begin
      if(rising_edge(clk0)) then
        if(user_rst_r = '1') then
          rd_cmd <= '0';
        elsif(rd_en = '0') then
          rd_cmd <= '1';
        else
          rd_cmd <= '0';
        end if;
      end if;
    end process;

    process(clk0)
    begin
      if(rising_edge(clk0)) then
        rd_en_i <= not rd_en;
      end if;
    end process;
  end generate;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        rden_cnt_clk0 <= "0000";
      -- Increment count for SRL. This count determines the number of clocks
      -- two clock command window is delayed until the Read data is matched
      -- with pattern data.
      elsif((rd_stb_cnt = "01") and (write_cal_start = '1') and
            (we_cal_done_i = '0') and (BURST_LENGTH = 4)) then
        rden_cnt_clk0 <= rden_cnt_clk0 + 1;
      elsif((rd_en = '0') and (rd_en_i = '1') and (write_cal_start = '1') and
            (we_cal_done_i = '0') and (BURST_LENGTH = 2)) then
        rden_cnt_clk0 <= rden_cnt_clk0 + 1;
      elsif ((we_cal_done_i = '1') and (we_cal_done_r = '0')) then
        rden_cnt_clk0 <= rden_cnt_clk0 - 1;
      else
        rden_cnt_clk0 <= rden_cnt_clk0;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        we_cal_done_r <= '0';
      else
        we_cal_done_r <= we_cal_done_i;
      end if;
    end if;
  end process;

  SRL_RDEN_CLK0 : SRL16
    port map(
      Q   => rden_srl_clk0,
      A0  => std_logic(rden_cnt_clk0(0)),
      A1  => std_logic(rden_cnt_clk0(1)),
      A2  => std_logic(rden_cnt_clk0(2)),
      A3  => std_logic(rden_cnt_clk0(3)),
      CLK => clk0,
      D   => rd_cmd
      );

  WE_CLK0_INST : FDRSE
    generic map (
      INIT => '0'
      )
    port map (
      Q  => rdfifo_we_i,
      C  => clk0,
      CE => '1',
      D  => rden_srl_clk0,
      R  => '0',
      S  => '0'
      );

  rdfifo_we <= rdfifo_we_i;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        we_cal_cnt <= "000";
      elsif((we_cal_start = '1') or (we_cal_cnt /= "000")) then
        we_cal_cnt <= we_cal_cnt + 1;
      else
        we_cal_cnt <= we_cal_cnt;
      end if;
    end if;
  end process;

  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_r = '1') then
        write_cal_start <= '0';
      elsif(we_cal_cnt = "111") then
        write_cal_start <= '1';
      else
        write_cal_start <= write_cal_start;
      end if;
    end if;
  end process;

  srl_count <= std_logic_vector(rden_cnt_clk0);

end arch_qdrii_phy_dly_cal_sm;
