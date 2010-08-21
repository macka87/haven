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
--  /   /         Filename           : qdrii_phy_init_sm.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Is the initialization statemachine generating the dummy write and
--     dummy read commands for delay calibration before regular memory
--     transactions begin.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity qdrii_phy_init_sm is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4;
    CLK_FREQ     : integer := 300;
    SIM_ONLY     : integer := 0
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
end entity qdrii_phy_init_sm;

architecture arch_qdrii_phy_init_sm of qdrii_phy_init_sm is

  constant ones : unsigned(10 downto 0) := (others => '1');

  constant CQ_WAIT         : std_logic_vector(13 downto 0):= "00000000000001";--1
  constant CAL_WR1         : std_logic_vector(13 downto 0):= "00000000000010";--2
  constant CAL_CQ_RD1      : std_logic_vector(13 downto 0):= "00000000000100";--4
  constant CAL_CQ_RD_WAIT1 : std_logic_vector(13 downto 0):= "00000000001000";--8
  constant CAL_WR2_A       : std_logic_vector(13 downto 0):= "00000000010000";--10
  constant CAL_WR2_B       : std_logic_vector(13 downto 0):= "00000000100000";--10
  constant CAL_CQ_RD2_A    : std_logic_vector(13 downto 0):= "00000001000000";--20
  constant CAL_CQ_RD2_B    : std_logic_vector(13 downto 0):= "00000010000000";--20
  constant CAL_CQ_RD_WAIT2 : std_logic_vector(13 downto 0):= "00000100000000";--40
  constant CAL_EN_RD_START : std_logic_vector(13 downto 0):= "00001000000000";--80
  constant CAL_EN_RD_A     : std_logic_vector(13 downto 0):= "00010000000000";--100
  constant CAL_EN_RD_B     : std_logic_vector(13 downto 0):= "00100000000000";--100
  constant CAL_EN_RD_WAIT  : std_logic_vector(13 downto 0):= "01000000000000";--200
  constant CAL_DONE_ST     : std_logic_vector(13 downto 0):= "10000000000000";--400

  signal dummy_rd_cnt        : unsigned(3 downto 0);
  signal dummy_cnt_en        : std_logic;
  signal phy_init_ns         : std_logic_vector(13 downto 0);
  signal phy_init_cs         : std_logic_vector(13 downto 0);
  signal cq_cnt              : unsigned(10 downto 0);
  signal cq_active           : std_logic;
  signal cal_done_r          : std_logic;
  signal cal_done_2r         : std_logic;
  signal cal_done_3r         : std_logic;
  signal cal_done_4r         : std_logic;
  signal cal_done_5r         : std_logic;
  signal dly_ready_r         : std_logic;
  signal dly_ready_2r        : std_logic;
  signal init_count          : unsigned(7 downto 0);
  signal init_cnt_done_i     : std_logic;
  signal we_cal_start_i      : std_logic;
  signal cal_done_i          : std_logic;
  signal q_init_delay_done_i : std_logic;

  signal init_max_count : integer range 0 to 350;

begin

  init_cnt_done <= init_cnt_done_i;
  we_cal_start  <= we_cal_start_i;
  cal_done      <= cal_done_i;

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_0 = '1') then
        q_init_delay_done_i <= '0';
      else
        q_init_delay_done_i <= q_init_delay_done;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        init_count <= (others => '0');
      elsif(init_count = X"C8") then
        init_count <= (others => '0');
      elsif(init_cnt_done_i = '0') then
        init_count <= init_count + 1;
      else
        init_count <= init_count;
      end if;
    end if;
  end process;

   --init_max_count generates a 200 us counter based on init_count
   -- an init_max_count of 8'hC8 refers to a 200 us count

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        if(SIM_ONLY = 1) then
          init_max_count <= CLK_FREQ;
        else
          init_max_count <= 0;
        end if;
      elsif((init_count = X"C8") and (init_cnt_done_i = '0')) then
        init_max_count <= init_max_count + 1;
      else
        init_max_count <= init_max_count;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        init_cnt_done_i <= '0';
      elsif(init_max_count = CLK_FREQ) then
        init_cnt_done_i <= '1';
      else
        init_cnt_done_i <= init_cnt_done_i;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        we_cal_start_i <= '0';
      elsif(dummy_cnt_en = '1') then
        we_cal_start_i <= '1';
      else
        we_cal_start_i <= we_cal_start_i;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        cq_cnt <= (others => '0');
      elsif((init_cnt_done_i = '1') and (cq_cnt /= ones)) then
        cq_cnt <= cq_cnt + 1;
      else
        cq_cnt <= cq_cnt;
      end if;
    end if;
  end process;

  process (clk0)
  --Make sure CQ clock is established (1024 clocks) before starting calibration
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        cq_active <= '0';
      elsif(cq_cnt = ones) then
        cq_active <= '1';
      else
        cq_active <= cq_active;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        dly_ready_r  <= '0';
        dly_ready_2r <= '0';
      else
        dly_ready_r  <= dly_ready;
        dly_ready_2r <= dly_ready_r;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        dly_cal_start <= '0';
      elsif((cq_active = '1') and (dly_ready_2r = '1')) then
        dly_cal_start <= '1';
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        dummy_rd_cnt <= "0000";
      elsif(dummy_cnt_en = '1') then
        dummy_rd_cnt <= "1111";
      elsif(dummy_rd_cnt /= "0000") then
        dummy_rd_cnt <= dummy_rd_cnt - 1;
      else
        dummy_rd_cnt <= dummy_rd_cnt;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        cal_done_r <= '0';
      elsif((en_cal_done = '1') and (dummy_rd_cnt = "0000")) then
        cal_done_r <= '1';
      else
        cal_done_r <= cal_done_r;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        cal_done_2r <= '0';
        cal_done_3r <= '0';
        cal_done_4r <= '0';
        cal_done_5r <= '0';
        cal_done_i  <= '0';
      else
        cal_done_2r <= cal_done_r;
        cal_done_3r <= cal_done_2r;
        cal_done_4r <= cal_done_3r;
        cal_done_5r <= cal_done_4r;
        cal_done_i  <= cal_done_5r;
      end if;
    end if;
  end process;

  -- synthesis translate_off
  process(cal_done_i)
  begin
    if(user_rst_0 = '0') then
      if(cal_done_i'event and cal_done_i = '1')then
        report "Calibration completed at time " & time'image(now);
      end if;
    end if;
  end process;
  -- synthesis translate_on

  process (clk0)
  begin
    if(clk0'event and clk0 = '1') then
      if(user_rst_0 = '1') then
        phy_init_cs <= CQ_WAIT;
      else
        phy_init_cs <= phy_init_ns;
      end if;
    end if;
  end process;

  process (phy_init_cs, cq_active, dly_ready_2r, q_init_delay_done, dly_cal_done,
           cal_done_i, en_cal_done, dummy_rd_cnt, q_init_delay_done_i)
  begin
    dummy_write  <= "00";
    dummy_read   <= "00";
    dummy_cnt_en <= '0';

    case (phy_init_cs) is
      when CQ_WAIT =>
        dummy_write <= "00";
        dummy_read  <= "00";
        if((cq_active = '1') and (dly_ready_2r = '1')) then
          phy_init_ns <= CAL_WR1;
        else
          phy_init_ns <= CQ_WAIT;
        end if;

      -- First Stage Calibration-Single Write command
      when CAL_WR1 =>
        dummy_write <= "01";
        dummy_read  <= "00";
        phy_init_ns <= CAL_CQ_RD1;

      -- First Stage Calibration- Continous Read commands until first stage
      -- calibration is complete.
      -- For BL4 read commands are issued on alternate clock.
      -- For BL2 read commands are issued on every clock.
      when CAL_CQ_RD1 =>
        dummy_write <= "00";
        dummy_read  <= "01";
        if(BURST_LENGTH = 2) then
          if(q_init_delay_done_i = '1') then
            phy_init_ns <= CAL_WR2_A;
          else
            phy_init_ns <= CAL_CQ_RD1;
          end if;
        elsif(BURST_LENGTH = 4) then
          phy_init_ns <= CAL_CQ_RD_WAIT1;
        end if;

      when CAL_CQ_RD_WAIT1 =>
        dummy_write <= "00";
        dummy_read  <= "00";
        if(q_init_delay_done = '1') then
          phy_init_ns <= CAL_WR2_A;
        else
          phy_init_ns <= CAL_CQ_RD1;
        end if;

      -- Second Stage Calibration-Write command
      -- For BL4 a single Write command is issued.
      -- For BL2 two Write commands are issued.
      when CAL_WR2_A =>
        dummy_write <= "10";
        dummy_read  <= "00";
        if(BURST_LENGTH = 2) then
          phy_init_ns <= CAL_WR2_B;
        elsif(BURST_LENGTH = 4) then
          phy_init_ns <= CAL_CQ_RD2_A;
        end if;

      when CAL_WR2_B =>
        dummy_write <= "11";
        dummy_read  <= "00";
        phy_init_ns <= CAL_CQ_RD2_A;

      -- Second Stage Calibration-Continous Read Commands until Second stage
      -- calibration is complete.
      -- For BL4 read commands are issued on alternate clocks.
      -- For BL2 read commands are issued on every clock.
      when CAL_CQ_RD2_A =>
        dummy_write <= "00";
        dummy_read  <= "01";
        if(BURST_LENGTH = 2) then
          phy_init_ns <= CAL_CQ_RD2_B;
        elsif(BURST_LENGTH = 4) then
          phy_init_ns <= CAL_CQ_RD_WAIT2;
        end if;

      when CAL_CQ_RD2_B =>
        dummy_write <= "00";
        dummy_read  <= "10";
        if(dly_cal_done = '1') then
          phy_init_ns <= CAL_EN_RD_START;
        else
          phy_init_ns <= CAL_CQ_RD2_A;
        end if;

      when CAL_CQ_RD_WAIT2 =>
        dummy_write <= "00";
        dummy_read  <= "00";
        if(dly_cal_done = '1') then
          phy_init_ns <= CAL_EN_RD_START;
        else
          phy_init_ns <= CAL_CQ_RD2_A;
        end if;

       -- Third Stage Calibration-Read Enable Calibration start
       when CAL_EN_RD_START =>
         dummy_write  <= "00";
         dummy_read   <= "00";
         dummy_cnt_en <= '1';
         phy_init_ns  <= CAL_EN_RD_WAIT;

       -- Third Stage Calibration-Read commands until Third Stage Calibration
       -- is complete (en_cal_done = '1');
       -- For BL4 a single Read command for every dummy_rd_cnt=4'd0.
       -- For BL2, two consecutive Read commands for every dummy_rd_cnt=4'd0.
       when CAL_EN_RD_A =>
         dummy_write  <= "00";
         dummy_read   <= "01";
         dummy_cnt_en <= '1';
         if(BURST_LENGTH = 2) then
           phy_init_ns <= CAL_EN_RD_B;
         elsif(BURST_LENGTH = 4) then
           phy_init_ns <= CAL_EN_RD_WAIT;
         end if;

       when CAL_EN_RD_B =>
         dummy_write  <= "00";
         dummy_read   <= "10";
         dummy_cnt_en <= '1';
         phy_init_ns  <= CAL_EN_RD_WAIT;

       when CAL_EN_RD_WAIT =>
         dummy_write <= "00";
         dummy_read  <= "00";
         if (cal_done_i = '1') then
           phy_init_ns <= CAL_DONE_ST;
         elsif ((en_cal_done = '0') and (dummy_rd_cnt = "0000")) then
           phy_init_ns <= CAL_EN_RD_A;
         else
           phy_init_ns <= CAL_EN_RD_WAIT;
         end if;

       when CAL_DONE_ST =>
         dummy_write <= "00";
         dummy_read  <= "00";
         phy_init_ns <= CAL_DONE_ST;

       when others =>
         dummy_write <= "00";
         dummy_read  <= "00";
         phy_init_ns <= CQ_WAIT;
    end case;
  end process;

end architecture arch_qdrii_phy_init_sm;
