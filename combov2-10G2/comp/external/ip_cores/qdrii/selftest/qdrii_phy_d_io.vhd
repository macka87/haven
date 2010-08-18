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
--  /   /         Filename           : qdrii_phy_d_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Is the I/O module of the QDR Write data, using ODDR Flip flops.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity  qdrii_phy_d_io is
  port(
    clk270 : in std_logic;
    dwl    : in std_logic;
    dwh    : in std_logic;
    qdr_d  : out std_logic
    );
end entity qdrii_phy_d_io;

architecture arch_qdrii_phy_d_io of qdrii_phy_d_io is

  signal qdr_d_int : std_logic;

begin

  ODDR_QDR_D : ODDR
    generic map(
      DDR_CLK_EDGE => "SAME_EDGE"
      )
    port map(
      Q  => qdr_d_int,
      C  => clk270,
      CE => '1',
      D1 => dwh,
      D2 => dwl,
      R  => '0',
      S  => '0'
      );

  QDR_D_OBUF : OBUFT
    port map (
      I => qdr_d_int,
      O => qdr_d,
      T => '0'
      );

end architecture arch_qdrii_phy_d_io;