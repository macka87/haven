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
--  /   /         Filename           : qdrii_test_wr_rd_sm.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. generates writes and read commands emulating the user backend.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

entity qdrii_test_wr_rd_sm is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4
    );
  port(
    clk          : in std_logic;
    reset        : in std_logic;
    cal_done     : in std_logic;
    user_wr_full : in std_logic;
    user_rd_full : in std_logic;
    test_w_n     : out std_logic;
    user_ad_w_n  : out std_logic;
    user_d_w_n   : out std_logic;
    user_r_n     : out std_logic;
    wr_begin     : out std_logic
    );
end entity qdrii_test_wr_rd_sm;

architecture arch_qdrii_test_wr_rd_sm of qdrii_test_wr_rd_sm is

  constant INIT       : std_logic_vector(4 downto 0) := "00001";
  constant IDLE       : std_logic_vector(4 downto 0) := "00010";
  constant TEST_WR    : std_logic_vector(4 downto 0) := "00100";
  constant TEST_RD    : std_logic_vector(4 downto 0) := "01000";
  constant TEST_WR_RD : std_logic_vector(4 downto 0) := "10000";
  --4 states - one-hot encoded

  signal current_state  : std_logic_vector(4 downto 0);
  signal next_state     : std_logic_vector(4 downto 0);
  signal test_r_n       : std_logic;
  signal test_w_n_i     : std_logic;

begin

  test_w_n <= test_w_n_i;
  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        current_state <= INIT;
      else
        current_state <= next_state;
      end if;
    end if;
  end process;

  process (current_state, user_wr_full, user_rd_full, cal_done)
  begin
    test_w_n_i <= '1';
    test_r_n <= '1';
    wr_begin <= '0';
    case (current_state) is
      when  INIT =>
        if (cal_done = '1') then
           next_state <=  IDLE;
        else
           next_state <= INIT;
        end if;

      when IDLE =>
        wr_begin <= '1';
        if ((user_wr_full and user_rd_full) = '1') then
           next_state <=  IDLE;
        elsif (((not(user_wr_full)) = '1') and (BURST_LENGTH = 4))then
           next_state <=  TEST_WR;
        elsif (((user_wr_full and (not(user_rd_full))) = '1') and (BURST_LENGTH = 4))then
           next_state <= TEST_RD;
        else
           next_state <= TEST_WR_RD;
        end if;

      -- Initiate a write cycle
      when TEST_WR =>
        wr_begin <= '1';
        test_w_n_i <= '0';
        if (user_rd_full = '1') then
           next_state <=  IDLE;
        else
           next_state <=  TEST_RD;
        end if;

      -- Initiate a read cycle
      when  TEST_RD =>
        wr_begin <= '1';
        test_r_n <= '0';
        if (user_wr_full = '1') then
           next_state <= IDLE;
        else
           next_state <= TEST_WR;
        end if;

      -- BL2 design Write-Read state. For BL2 Write and Read command can be
      -- issued in the same clock.
      when TEST_WR_RD =>
        wr_begin <= '1';
        if(user_wr_full = '0') then
          test_w_n_i <= '0';
        end if;
        if(user_rd_full = '0') then
          test_r_n <= '0';
        end if;
        if((user_wr_full = '1') and (user_rd_full = '1')) then
          next_state <= IDLE;
        else
          next_state <= TEST_WR_RD;
        end if;

      when others =>
        next_state <=  INIT;
    end case;
  end process;

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        user_d_w_n  <= '1';
        user_ad_w_n <= '1';
        user_r_n    <= '1';
      else
        user_d_w_n  <= test_w_n_i;
        user_ad_w_n <= test_w_n_i;
        user_r_n    <= test_r_n;
      end if;
    end if;
  end process;

end architecture arch_qdrii_test_wr_rd_sm;
