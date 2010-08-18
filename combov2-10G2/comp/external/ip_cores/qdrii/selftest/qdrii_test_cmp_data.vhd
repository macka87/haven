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
--  /   /         Filename           : qdrii_test_cmp_data.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Incorporates a one bit comparision scheme.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_test_cmp_data is
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
end entity qdrii_test_cmp_data;

architecture arch_qdrii_test_cmp_data of qdrii_test_cmp_data is

begin

  process (clk)
  begin
    if(clk'event and clk = '1') then
      if(reset = '1') then
        cmp_lsb <= '0';
        cmp_msb <= '0';
      elsif(cmp_en = '1') then
        cmp_lsb <= (user_qrl xor dwl_comp);
        cmp_msb <= (user_qrh xor dwh_comp);
      end if;
    end if;
  end process;

end architecture arch_qdrii_test_cmp_data;