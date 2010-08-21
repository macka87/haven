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
--  /   /         Filename           : infrastructure.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Distributes various phases of the system clock
--       2. Generation and distribution of reset from the input clock.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_infrastructure is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    RST_ACT_LOW : integer := 1
    );
  port(
    sys_rst_n       : in  std_logic;
    idelay_ctrl_rdy : in  std_logic;
    dcm_locked      : in  std_logic;
    clk0            : in  std_logic;
    clk180          : in  std_logic;
    clk270          : in  std_logic;
    clk200          : in  std_logic;
    user_rst_0      : out std_logic;
    user_rst_180    : out std_logic;
    user_rst_270    : out std_logic;
    user_rst_200    : out std_logic
    );
end qdrii_infrastructure;

architecture arch_qdrii_infrastructure of qdrii_infrastructure is

  constant RST_SYNC_NUM : integer range 10 to 30 := 25;

  signal rst0_sync_r   : std_logic_vector(RST_SYNC_NUM-1 downto 0);
  signal rst180_sync_r : std_logic_vector(RST_SYNC_NUM-1 downto 0);
  signal rst270_sync_r : std_logic_vector(RST_SYNC_NUM-1 downto 0);
  signal rst200_sync_r : std_logic_vector(RST_SYNC_NUM-1 downto 0);
  signal user_reset_in : std_logic;
  signal rst_tmp       : std_logic;
  signal clk0_i        : std_logic;
  signal clk180_i      : std_logic;
  signal clk270_i      : std_logic;
  signal clk200_i      : std_logic;

  attribute syn_maxfan : integer;
  attribute max_fanout : integer;
  attribute buffer_type : string;
  attribute syn_maxfan of rst0_sync_r : signal is 10;
  attribute max_fanout of rst0_sync_r : signal is 10;
  attribute buffer_type of rst0_sync_r : signal is "none";
  attribute syn_maxfan of rst180_sync_r : signal is 10;
  attribute max_fanout of rst180_sync_r : signal is 10;
  attribute syn_maxfan of rst270_sync_r : signal is 10;
  attribute max_fanout of rst270_sync_r : signal is 10;
  attribute syn_maxfan of rst200_sync_r : signal is 10;
  attribute max_fanout of rst200_sync_r : signal is 10;

  begin

  clk0_i   <= clk0;
  clk180_i <= clk180;
  clk270_i <= clk270;
  clk200_i <= clk200;

  user_reset_in <= not(sys_rst_n) when (RST_ACT_LOW = 1) else sys_rst_n;

  rst_tmp <= (not(dcm_locked)) or (not(idelay_ctrl_rdy)) or user_reset_in;

  process(clk0_i, rst_tmp)
  begin
    if(rst_tmp = '1') then
      rst0_sync_r <= (others => '1');
    elsif(clk0_i'event and clk0_i = '1') then
      rst0_sync_r <= (rst0_sync_r(RST_SYNC_NUM-2 downto 0) & '0');
    end if;
  end process;

  process(clk180_i, rst_tmp)
  begin
    if(rst_tmp = '1') then
      rst180_sync_r <= (others => '1');
    elsif(clk180_i'event and clk180_i = '1') then
      rst180_sync_r <= (rst180_sync_r(RST_SYNC_NUM-2 downto 0) & '0');
    end if;
  end process;

  process(clk270_i, rst_tmp)
  begin
    if(rst_tmp = '1') then
      rst270_sync_r <= (others => '1');
    elsif(clk270_i'event and clk270_i = '1') then
      rst270_sync_r <= (rst270_sync_r(RST_SYNC_NUM-2 downto 0) & '0');
    end if;
  end process;

  process(clk200_i, dcm_locked)
  begin
    if(dcm_locked = '0') then
      rst200_sync_r <= (others => '1');
    elsif(clk200_i'event and clk200_i = '1') then
      rst200_sync_r <= (rst200_sync_r(RST_SYNC_NUM-2 downto 0) & '0');
    end if;
  end process;

  user_rst_0   <= rst0_sync_r(RST_SYNC_NUM-1);
  user_rst_180 <= rst180_sync_r(RST_SYNC_NUM-1);
  user_rst_270 <= rst270_sync_r(RST_SYNC_NUM-1);
  user_rst_200 <= rst200_sync_r(RST_SYNC_NUM-1);

end architecture arch_qdrii_infrastructure;
