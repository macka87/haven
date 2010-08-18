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
--  /   /         Filename           : qdrii_idelay_ctrl.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. instantiates IDELAYCTRL primitives to generate the IDELAY ready
--          signal. This uses the 200 MHz reference clock input.
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;


entity qdrii_idelay_ctrl is
  port  (
   clk200          : in  std_logic;
   user_rst_200    : in  std_logic;
   idelay_ctrl_rdy : out std_logic
   );
end entity qdrii_idelay_ctrl;

architecture arch_qdrii_idelay_ctrl of  qdrii_idelay_ctrl is

  ------------------------------------------------------------------------------
  -- The following constant "IDELAYCTRL_NUM" indicates the number of
  -- IDELAYCTRLs that are LOCed for the design. The IDELAYCTRL LOCs are
  -- provided in the UCF file of par folder. MIG provides the constant value
  -- and the LOCs in the UCF file based on the selected Data Read banks for
  -- the design. You must not alter this value unless it is needed. If you
  -- modify this value, you should make sure that the value of "IDELAYCTRL_NUM"
  -- and IDELAYCTRL LOCs in UCF file are same and are relavent to the Data Read
  -- banks used.
  ------------------------------------------------------------------------------
  constant IDELAYCTRL_NUM : integer := 2;

  constant ONES : std_logic_vector(IDELAYCTRL_NUM-1 downto 0) := (others => '1');

  signal idelay_ctrl_rdy_i : std_logic_vector(IDELAYCTRL_NUM-1 downto 0);

begin

  IDELAYCTRL_INST : for bnk_i in 0 to IDELAYCTRL_NUM-1 generate
    U_IDELAYCTRL : IDELAYCTRL
     port map (
       RDY    => idelay_ctrl_rdy_i(bnk_i),
       REFCLK => clk200,
       RST    => user_rst_200
       );
  end generate IDELAYCTRL_INST;

  idelay_ctrl_rdy <= '1' when (idelay_ctrl_rdy_i = ONES) else
                    '0';

end architecture arch_qdrii_idelay_ctrl;