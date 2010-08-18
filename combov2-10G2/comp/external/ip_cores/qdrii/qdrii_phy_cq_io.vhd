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
--   Rev 1.1 - Parameter IODELAY_GRP added and constraint IODELAY_GROUP added
--             on IODELAY primitives. PK. 11/27/08
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_cq_io is
  generic(
    HIGH_PERFORMANCE_MODE : boolean := TRUE;
    IODELAY_GRP           : string  := "IODELAY_MIG"
    );
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

  attribute IODELAY_GROUP : string;
  attribute IODELAY_GROUP of U_IODELAY : label is IODELAY_GRP;

begin
--******************************************************************************
-- CQ path inside the IOB
--******************************************************************************

  QDR_CQ_IBUF : IBUF
    port map (
     I => qdr_cq,
     O => qdr_cq_int
    );

  U_IODELAY : IODELAY
    generic map(
      DELAY_SRC             => "I",
      IDELAY_TYPE           => "VARIABLE",
      HIGH_PERFORMANCE_MODE => HIGH_PERFORMANCE_MODE,
      IDELAY_VALUE          => 0,
      ODELAY_VALUE          => 0
      )
    port map(
      DATAOUT => qdr_cq_delay,
      C       => cal_clk,
      CE      => cq_dly_ce,
      DATAIN  => '0',
      IDATAIN => qdr_cq_int,
      INC     => cq_dly_inc,
      ODATAIN => '0',
      RST     => cq_dly_rst,
      T       => '1'
      );

--  QDR_CQ_IDELAY :  IDELAY
--    generic map (
--     IOBDELAY_TYPE  => "VARIABLE",
--     IOBDELAY_VALUE => 0
--     )
--    port map (
--     O   => qdr_cq_delay,
--     C   => cal_clk,
--     CE  => cq_dly_ce,
--     I   => qdr_cq_int,
--     INC => cq_dly_inc,
--     RST => cq_dly_rst
--     );

  QDR_CQ_BUFIO_INST : BUFIO
    port map (
      I => qdr_cq_delay,
      O => qdr_cq_bufio_w
      );

  qdr_cq_bufio <= qdr_cq_bufio_w after 1000 ps;

end architecture arch_qdrii_phy_cq_io;