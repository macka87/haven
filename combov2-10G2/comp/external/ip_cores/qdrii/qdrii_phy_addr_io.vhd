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
--  /   /         Filename           : qdrii_phy_addr_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Instantiates the I/O module for generating the addresses to the memory
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_phy_addr_io is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    ADDR_WIDTH   : integer := 19;
    BURST_LENGTH : integer := 4
    );
  port (
    clk180          : in  std_logic;
    clk270          : in  std_logic;
    user_rst_180    : in  std_logic;
    user_rst_270    : in  std_logic;
    wr_init_n       : in  std_logic;
    rd_init_n       : in  std_logic;
    dummy_write     : in  std_logic_vector(1 downto 0);
    dummy_read      : in  std_logic_vector(1 downto 0);
    fifo_ad_wr      : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    fifo_ad_rd      : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    cal_done        : in  std_logic;
    rd_init_delay_n : in  std_logic;
    qdr_sa          : out std_logic_vector(ADDR_WIDTH-1 downto 0)
    );
end entity qdrii_phy_addr_io;

architecture arch_qdrii_phy_addr_io of qdrii_phy_addr_io is

  signal qdr_sa_int     : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal address_int_ff : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_wr_r   : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_rd_r   : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_wr_2r  : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_rd_2r  : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_wr_3r  : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal fifo_ad_rd_3r  : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal wr_init_n_r    : std_logic;
  signal rd_init_n_r    : std_logic;
  signal dummy_write_r  : std_logic_vector(1 downto 0);
  signal dummy_read_r   : std_logic_vector(1 downto 0);

  attribute syn_useioff : boolean;
  attribute IOB : string;

begin

  process (clk270)
  begin
    if(rising_edge(clk270)) then
      fifo_ad_wr_r <= fifo_ad_wr;
      fifo_ad_rd_r <= fifo_ad_rd;
    end if;
  end process;

  BL4_INST : if(BURST_LENGTH = 4) generate
  -- For BL4 address is SDR
  begin
    process (clk270)
    begin
      if(rising_edge(clk270)) then
--        if((user_rst_270 = '1') or (cal_done = '0')) then
        if(cal_done = '0') then
           address_int_ff <= (others=>'0');
        elsif (rd_init_delay_n = '1') then
           address_int_ff <= fifo_ad_wr_r;
        else
           address_int_ff <= fifo_ad_rd_r;
        end if;
      end if;
    end process;
  end generate;

  BL2_INST : if(BURST_LENGTH = 2) generate
  -- For BL2 address is DDR. A read command by the controller is associated
  -- with read address bits and write command by the controller is associated
  -- with write address bits on to the IO bus. Absence of any commands is
  -- associated with address bits on IO bus tied to logic 0.
  begin

--    process (clk270)
--    begin
--      if(rising_edge(clk270)) then
--        if(user_rst_270 = '1') then
--          wr_init_n_r <= '0';
--          rd_init_n_r <= '0';
--        else
--          wr_init_n_r <= wr_init_n;
--          rd_init_n_r <= rd_init_n;
--        end if;
--      end if;
--    end process;

    process (clk270)
    begin
      if(rising_edge(clk270)) then
        wr_init_n_r <= wr_init_n;
        rd_init_n_r <= rd_init_n;
      end if;
    end process;

    process (clk270)
    begin
      if(rising_edge(clk270)) then
        dummy_write_r <= dummy_write;
        dummy_read_r  <= dummy_read;
      end if;
    end process;

    process(clk270)
    begin
      if(rising_edge(clk270)) then
        if((BURST_LENGTH = 2) and (dummy_write_r = "11")) then
          fifo_ad_wr_2r(ADDR_WIDTH-1 downto 1) <= (others =>'0');
          fifo_ad_wr_2r(0)                     <= '1';
        elsif((BURST_LENGTH = 2) and (dummy_read_r = "10")) then
          fifo_ad_rd_2r(ADDR_WIDTH-1 downto 1) <= (others =>'0');
          fifo_ad_rd_2r(0)                     <= '1';
        elsif ((wr_init_n_r = '0') or (rd_init_n_r = '0')) then
          fifo_ad_wr_2r <= fifo_ad_wr_r;
          fifo_ad_rd_2r <= fifo_ad_rd_r;
        else
          fifo_ad_wr_2r <= (others => '0');
          fifo_ad_rd_2r <= (others => '0');
        end if;
      end if;
    end process;

    process(clk270)
    begin
      if(rising_edge(clk270)) then
        fifo_ad_rd_3r <= fifo_ad_rd_2r;
        fifo_ad_wr_3r <= fifo_ad_wr_2r;
      end if;
    end process;
  end generate;

  BL2_IOB_INST : if(BURST_LENGTH = 2) generate
    -- For BL2 address is DDR. write address is associated with falling edge
    -- of K clock. Read address is associated with rising edge of K clock.
    ADDR_INST : for i in 0 to ADDR_WIDTH-1 generate
      ODDR_QDR_SA : ODDR
        generic map(
          DDR_CLK_EDGE => "SAME_EDGE"
          )
        port map(
          Q  => qdr_sa_int(i),
          C  => clk270,
          CE => '1',
          D1 => fifo_ad_rd_3r(i),
          D2 => fifo_ad_wr_3r(i),
          R  => '0',
          S  => '0'
          );
    end generate ADDR_INST;
  end generate BL2_IOB_INST;


  BL4_IOB_INST : if(BURST_LENGTH = 4) generate
    -- For BL4 address is SDR. Read or Write address is always associated
    -- with rising edge of K clock.
    ADDR_INST : for i in 0 to ADDR_WIDTH-1 generate
      attribute syn_useioff of ADDRESS_FF : label is true;
      attribute IOB of ADDRESS_FF : label is "force";
    begin
      ADDRESS_FF : FDRSE
        generic map (
          INIT => '0'
          )
        port map (
          Q  => qdr_sa_int(i),
          C  => clk180,
          CE => '1',
          D  => address_int_ff(i),
          R  => '0',
          S  => '0'
          );
    end generate ADDR_INST;
  end generate BL4_IOB_INST;

  ADDR_II : for j in 0 to ADDR_WIDTH-1 generate
    IO_FF : OBUFT
      port map(
        I => qdr_sa_int(j),
        O => qdr_sa(j),
        T => '0'
        );
  end generate ADDR_II;

end architecture arch_qdrii_phy_addr_io;