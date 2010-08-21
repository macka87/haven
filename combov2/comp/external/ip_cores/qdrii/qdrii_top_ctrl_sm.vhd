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
--  /   /         Filename           : top_ctrl_sm.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Monitors Read / Write queue status from User Interface FIFOs and
--      generates strobe signals to launch Read / Write requests to
--      QDR II device.
--
--Revision History:
--
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_top_ctrl_sm is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4
    );
  port (
    clk0        : in std_logic;
    user_rst_0  : in std_logic;
    wr_empty    : in std_logic;
    rd_empty    : in std_logic;
    cal_done    : in std_logic;
    wr_init_n   : out std_logic;
    rd_init_n   : out std_logic
    );
end entity qdrii_top_ctrl_sm;

architecture arch_qdrii_top_ctrl_sm of qdrii_top_ctrl_sm is

  constant INIT       : std_logic_vector(2 downto 0) := "000";
  constant READ       : std_logic_vector(2 downto 0) := "001";
  constant WRITE      : std_logic_vector(2 downto 0) := "010";
  constant WRITE_READ : std_logic_vector(2 downto 0) := "011";
  constant IDLE       : std_logic_vector(2 downto 0) := "100";

  signal Current_State : std_logic_vector(2 downto 0);
  signal Next_State    : std_logic_vector(2 downto 0);

begin

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      if(user_rst_0 = '1') then
        Current_State <= INIT;
      else
        Current_State <= Next_State;
      end if;
    end if;
  end process;

  process(Current_State, wr_empty, rd_empty, cal_done)
  begin

    wr_init_n <= '1';
    rd_init_n <= '1';

    case(Current_State) is

      when INIT =>
        if (cal_done = '1') then
            Next_State <= IDLE;
        else
            Next_State <= INIT;
        end if;

      when IDLE =>
        wr_init_n <= '1';
        rd_init_n <= '1';
        if((wr_empty = '0') and (BURST_LENGTH = 4)) then
          Next_State <= WRITE;
        elsif ((rd_empty = '0') and (BURST_LENGTH = 4)) then
          Next_State <= READ;
        elsif (((rd_empty = '0') or (wr_empty = '0')) and (BURST_LENGTH = 2)) then
          next_state <= WRITE_READ;
        else
          Next_State <= IDLE;
        end if;

      when WRITE =>
        wr_init_n <= '0'; -- Initiate a write cycle
        rd_init_n <= '1';

        if(rd_empty = '0') then
          Next_State <= READ;
        else
          Next_State <= IDLE;
        end if;

      when READ =>
        rd_init_n <= '0';  -- Initiate a read cycle
        wr_init_n <= '1';

        if(wr_empty = '0') then
          Next_State <= WRITE;
        else
          Next_State <= IDLE;
        end if;

      -- BL2 design Write-Read state. For BL2 Write and Read command can be
      -- issued in the same clock(K-Clock).
      when WRITE_READ =>
        if(wr_empty = '0') then
          wr_init_n <= '0';
        end if;

        if(rd_empty = '0') then
          rd_init_n <= '0';
        end if;

        if((wr_empty = '1') and (rd_empty = '1')) then
          next_state <= IDLE;
        else
          next_state <= WRITE_READ;
        end if;

      when OTHERS =>
        wr_init_n  <= '1';
        rd_init_n  <= '1';
        Next_State <= IDLE;

    end case;
  end process;

end architecture arch_qdrii_top_ctrl_sm;