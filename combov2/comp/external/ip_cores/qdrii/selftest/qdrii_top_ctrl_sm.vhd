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
--------------------------------------------------------------------------------

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
    if(clk0'event and clk0 = '1') then
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
