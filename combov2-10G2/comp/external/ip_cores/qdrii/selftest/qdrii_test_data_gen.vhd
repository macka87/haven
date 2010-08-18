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
--  /   /         Filename           : qdrii_test_data_gen.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. generates test write data for the memory interface.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use unisim.vcomponents.all;

entity qdrii_test_data_gen is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BW_WIDTH   : integer := 8;
    DATA_WIDTH : integer := 72
    );
  port(
    clk           : in  std_logic;
    reset         : in  std_logic;
    user_w_n      : in  std_logic;
    test_w_n      : in  std_logic;
    user_qr_valid : in  std_logic;
    wr_begin      : in  std_logic;
    user_dwl      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    user_dwh      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    dwl_comp      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    dwh_comp      : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity qdrii_test_data_gen;

architecture arch_qdrii_test_data_gen of qdrii_test_data_gen is

  signal data_counter_wr        : unsigned(7 downto 0);
  signal data_counter_comp_l    : unsigned(7 downto 0);
  signal data_counter_comp_fall : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal data_counter_comp_rise : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

  -- Write Data to Memory

  process(clk)
   begin
     if(clk'event and clk = '1') then
       if(reset = '1') then
         data_counter_wr <= (others => '0');
       elsif(user_qr_valid = '1') then
         data_counter_wr <= data_counter_wr + 1;
       end if;
     end if;
  end process;

  COMP_DATA : for bwi in 0 to BW_WIDTH-1 generate
    dwl_comp(((bwi+1)*9)-1 downto (bwi*9)) <= std_logic_vector(data_counter_wr & '1');
    dwh_comp(((bwi+1)*9)-1 downto (bwi*9)) <= std_logic_vector(data_counter_wr & '0');
  end generate COMP_DATA;

  process(clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        data_counter_comp_l <= (others => '0');
      elsif(test_w_n = '0' or user_w_n = '0') then
        data_counter_comp_l <= data_counter_comp_l + 1;
      end if;
    end if;
  end process;

  USER_DATA : for bwii in 0 to BW_WIDTH-1 generate
    data_counter_comp_fall(((bwii+1)*9)-1 downto (bwii*9)) <= std_logic_vector(data_counter_comp_l & '1');
    data_counter_comp_rise(((bwii+1)*9)-1 downto (bwii*9)) <= std_logic_vector(data_counter_comp_l & '0');
  end generate USER_DATA;

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        user_dwl <= (others => '0');
        user_dwh <= (others => '0');
      elsif (wr_begin = '1') then
        user_dwl <= data_counter_comp_fall(DATA_WIDTH-1 downto 0);
        user_dwh <= data_counter_comp_rise(DATA_WIDTH-1 downto 0);
      end if;
    end if;
  end process;

end architecture arch_qdrii_test_data_gen;