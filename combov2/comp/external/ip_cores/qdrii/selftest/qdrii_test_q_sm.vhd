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
--  /   /         Filename           : qdrii_test_q_sm.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. generates the compare data and compares the write data against the
--          captured read data.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;


entity qdrii_test_q_sm is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    DATA_WIDTH : integer := 72
    );
  port(
    clk           : in  std_logic;
    reset         : in  std_logic;
    cal_done      : in  std_logic;
    user_qr_valid : in  std_logic;
    user_qrl      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_qrh      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    dwl_comp      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    dwh_comp      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    compare_error : out std_logic
    );
end entity qdrii_test_q_sm;

architecture arch_qdrii_test_q_sm of qdrii_test_q_sm is

  component qdrii_test_cmp_data
    port(
      clk      : in  std_logic;
      reset    : in  std_logic;
      cmp_en   : in  std_logic;
      user_qrh : in  std_logic;
      user_qrl : in  std_logic;
      dwh_comp : in  std_logic;
      dwl_comp : in  std_logic;
      cmp_lsb  : out std_logic;
      cmp_msb  : out std_logic
      );
  end component qdrii_test_cmp_data;

  constant zeros : std_logic_vector(DATA_WIDTH-1 downto 0) := (others => '0');

  signal compare_lsb     : std_logic;
  signal compare_msb     : std_logic;
  signal cmp_err         : std_logic;
  signal comp_lsb        : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal comp_msb        : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal comp_lsb_i      : std_logic;
  signal comp_msb_i      : std_logic;
  signal compare_error_i : std_logic;
  signal user_qrl_r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal user_qrh_r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dwl_comp_r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dwh_comp_r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal user_qrl_2r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal user_qrh_2r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dwl_comp_2r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dwh_comp_2r      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal compare_en_r    : std_logic;
  signal compare_en_2r    : std_logic;
begin

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        compare_en_r   <= '0';
        compare_en_2r <= '0';
      else
        compare_en_r <= user_qr_valid;
        compare_en_2r   <= compare_en_r;
      end if;
    end if;
  end process;

  process(clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        user_qrl_r  <= (others => '0');
        user_qrl_2r <= (others => '0');
        user_qrh_r  <= (others => '0');
        user_qrh_2r <= (others => '0');
        dwl_comp_r  <= (others => '0');
        dwl_comp_2r <= (others => '0');
        dwh_comp_r  <= (others => '0');
        dwh_comp_2r <= (others => '0');
      else
        user_qrl_r  <= user_qrl;
        user_qrl_2r <= user_qrl_r;
        user_qrh_r  <= user_qrh;
        user_qrh_2r <= user_qrh_r;
        dwl_comp_r  <= dwl_comp;
        dwl_comp_2r <= dwl_comp_r;
        dwh_comp_r  <= dwh_comp;
        dwh_comp_2r <= dwh_comp_r;
      end if;
    end if;
  end process;

  COMP_A : for comp_i in 0 to DATA_WIDTH-1 generate
    U_QDRII_TEST_CMP_DATA : qdrii_test_cmp_data
      port map(
        clk       => clk,
        reset     => reset,
        cmp_en    => compare_en_2r,
        user_qrh  => user_qrh_2r(comp_i),
        user_qrl  => user_qrl_2r(comp_i),
        dwh_comp  => dwh_comp_2r(comp_i),
        dwl_comp  => dwl_comp_2r(comp_i),
        cmp_lsb   => comp_lsb(comp_i),
        cmp_msb   => comp_msb(comp_i)
        );
  end generate COMP_A;

  comp_lsb_i <= '1' when (comp_lsb /= zeros) else '0';
  comp_msb_i <= '1' when (comp_msb /= zeros) else '0';

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        compare_lsb <= '0';
        compare_msb <= '0';
        cmp_err     <= '0';
      elsif(compare_en_2r = '1') then
        compare_lsb <= comp_lsb_i;
        compare_msb <= comp_msb_i;
        cmp_err     <= (compare_lsb or compare_msb);
      end if;
    end if;
  end process;

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        compare_error_i <= '0';
      elsif ((cmp_err = '0') and (compare_error_i = '0')) then
        compare_error_i <= '0';
      else
        compare_error_i <= '1';
      end if;
    end if;
  end process;

  --synthesis translate_off
  process (clk)
  begin
    if(clk'event and clk = '0') then
      if(compare_en_2r = '1') then
        assert(compare_error_i = '0')
          report "DATA ERROR at time " & time'image(now);
      end if;
    end if;
  end process;
  --synthesis translate_on

  process(clk)
  begin
    if(clk'event and clk = '0') then
      compare_error <= compare_error_i;
    end if;
  end process;

end architecture arch_qdrii_test_q_sm;