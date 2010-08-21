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
--  /   /         Filename           : qdrii_top_wr_data_interface.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Responsible for storing the Write data written by the user design.
--          Instantiates the FIFOs for storing the write data.
--
--Revision History:
--
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_top_wr_data_interface is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4;
    BW_WIDTH     : integer := 8;
    DATA_WIDTH   : integer := 72
    );
  port (
    clk0         : in  std_logic;
    user_rst_0   : in  std_logic;
    clk270       : in  std_logic;
    user_rst_270 : in  std_logic;
    cal_done     : in  std_logic;
    dummy_wrl    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    dummy_wrh    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    dummy_wren   : in  std_logic;
    user_w_n     : in  std_logic;
    user_bw_h    : in  std_logic_vector(BW_WIDTH-1 downto 0);
    user_bw_l    : in  std_logic_vector(BW_WIDTH-1 downto 0);
    user_dwl     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_dwh     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    wr_init2_n   : in  std_logic;
    fifo_dwl     : out std_logic_vector(DATA_WIDTH-1 downto 0);
    fifo_dwh     : out std_logic_vector(DATA_WIDTH-1 downto 0);
    fifo_bw_h    : out std_logic_vector(BW_WIDTH-1 downto 0);
    fifo_bw_l    : out std_logic_vector(BW_WIDTH-1 downto 0)
    );
end entity qdrii_top_wr_data_interface;

architecture arch_qdrii_top_wr_data_interface of qdrii_top_wr_data_interface is

   signal wrfifo_wren_r1       : std_logic;
   signal user_w_n_stretch     : std_logic;
   signal not_wr_init2_n       : std_logic;
   signal not_user_w_n_stretch : std_logic;
   signal user_fifo_bw_out     : std_logic_vector((2*BW_WIDTH)-1 downto 0);
   signal user_fifo_bw         : std_logic_vector((2*BW_WIDTH)-1 downto 0);
   signal user_fifo_bw_in      : std_logic_vector((2*BW_WIDTH)-1 downto 0);
   signal wrfifo_wren          : std_logic;
   signal wrfifo_wrdata_l      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal wrfifo_wrdata_h      : std_logic_vector(DATA_WIDTH-1 downto 0);

  component qdrii_top_wrdata_fifo
    generic(
      DATA_WIDTH : integer := DATA_WIDTH
      );
    port(
      clk0         : in  std_logic;
      clk270       : in  std_logic;
      user_rst_270 : in  std_logic;
      idata_lsb    : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      idata_msb    : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      rdenb        : in  std_logic;
      wrenb        : in  std_logic;
      odata_lsb    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      odata_msb    : out std_logic_vector(DATA_WIDTH - 1 downto 0)
      );
  end component qdrii_top_wrdata_fifo;

  component qdrii_top_wrdata_bw_fifo
    generic (
      BW_WIDTH : integer := BW_WIDTH
      );
    port(
      clk0         : in  std_logic;
      clk270       : in  std_logic;
      user_rst_270 : in  std_logic;
      idata        : in  std_logic_vector((2 * BW_WIDTH) - 1 downto 0);
      rdenb        : in  std_logic;
      wrenb        : in  std_logic;
      odata        : out std_logic_vector((2 * BW_WIDTH) - 1 downto 0)
      );
  end component qdrii_top_wrdata_bw_fifo;

begin

--  wrfifo_wren <= user_w_n and (not dummy_wren);
--  wrfifo_wrdata_l <= user_dwl or dummy_wrl;
--  wrfifo_wrdata_h <= user_dwh or dummy_wrh;

  wrfifo_wren <= user_w_n when (cal_done = '1') else
                 not(dummy_wren);

  wrfifo_wrdata_l <= user_dwl when (cal_done = '1') else
                     dummy_wrl;
  wrfifo_wrdata_h <= user_dwh when (cal_done = '1') else
                     dummy_wrh;

  BL4_INST : if(BURST_LENGTH = 4) generate
    USER_W_N_FF : FDRSE
      generic map (
        INIT => '1'
        )
      port map (
        Q  => wrfifo_wren_r1,
        C  => clk0,
        CE => '1',
        D  => wrfifo_wren,
        R  => '0',
        S  => '0'
        );

    user_w_n_stretch <= (wrfifo_wren and wrfifo_wren_r1);
  end generate BL4_INST;

  BL2_INST : if(BURST_LENGTH = 2) generate
    user_w_n_stretch <= wrfifo_wren;
  end generate BL2_INST;


   not_wr_init2_n       <= not(wr_init2_n);
   not_user_w_n_stretch <= not(user_w_n_stretch);

   U_QDRII_TOP_WRDATA_FIFO : qdrii_top_wrdata_fifo
     generic map (
       DATA_WIDTH => DATA_WIDTH
       )
     port map (
       clk0         => clk0,
       clk270       => clk270,
       user_rst_270 => user_rst_270,
       idata_lsb    => wrfifo_wrdata_l,
       idata_msb    => wrfifo_wrdata_h,
       rdenb        => not_wr_init2_n,
       wrenb        => not_user_w_n_stretch,
       odata_lsb    => fifo_dwl,
       odata_msb    => fifo_dwh
       );

   user_fifo_bw <= (user_bw_h(BW_WIDTH - 1 downto 0) &
                    user_bw_l(BW_WIDTH - 1 downto 0));

   user_fifo_bw_in <= user_fifo_bw when (cal_done = '1') else
                      (others => '0');

   U_QDRII_TOP_WRDATA_BW_FIFO : qdrii_top_wrdata_bw_fifo
     generic map (
       BW_WIDTH => BW_WIDTH
       )
     port map (
       clk0         => clk0,
       clk270       => clk270,
       user_rst_270 => user_rst_270,
       idata        => user_fifo_bw_in,
       rdenb        => not_wr_init2_n,
       wrenb        => not_user_w_n_stretch,
       odata        => user_fifo_bw_out
       );


   fifo_bw_l       <= user_fifo_bw_out(BW_WIDTH - 1 downto 0);
   fifo_bw_h       <= user_fifo_bw_out((2 * BW_WIDTH) - 1 downto BW_WIDTH);

end architecture arch_qdrii_top_wr_data_interface;