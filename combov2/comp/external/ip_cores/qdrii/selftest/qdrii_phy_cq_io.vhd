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
--  /   /         Filename           : qdrii_phy_cq_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--      1. Is the I/O module for the incoming memory read clock (CQ).
--      2. Instantiates the IDELAY to delay the clock and routes it through
--         BUFIO.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_cq_io is
  port(
    qdr_cq       : in  std_logic;
    cal_clk      : in  std_logic;
    cq_dly_ce    : in  std_logic;
    cq_dly_inc   : in  std_logic;
    cq_dly_rst   : in  std_logic;
    qdr_cq_bufio : out std_logic
    );
end entity qdrii_phy_cq_io;

architecture arch_qdrii_phy_cq_io of qdrii_phy_cq_io is

  signal qdr_cq_int     : std_logic;
  signal qdr_cq_delay   : std_logic;
  signal qdr_cq_bufio_w : std_logic;

begin
--******************************************************************************
-- CQ path inside the IOB
--******************************************************************************

  QDR_CQ_IBUF : IBUF
    port map (
     I => qdr_cq,
     O => qdr_cq_int
    );

  QDR_CQ_IDELAY :  IDELAY
    generic map (
     IOBDELAY_TYPE  => "VARIABLE",
     IOBDELAY_VALUE => 0
     )
    port map (
     O   => qdr_cq_delay,
     C   => cal_clk,
     CE  => cq_dly_ce,
     I   => qdr_cq_int,
     INC => cq_dly_inc,
     RST => cq_dly_rst
     );

  QDR_CQ_BUFIO_INST : BUFIO
    port map (
      I => qdr_cq_delay,
      O => qdr_cq_bufio_w
      );

  qdr_cq_bufio <= qdr_cq_bufio_w after 800 ps;

end architecture arch_qdrii_phy_cq_io;