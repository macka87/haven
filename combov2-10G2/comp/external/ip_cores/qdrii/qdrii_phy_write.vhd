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
--  /   /         Filename           : qdrii_phy_write.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Is the top level module for write data and commands
--  2. Instantiates the I/O modules for the memory write data, as well as
--     for the write command.
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_phy_write is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BURST_LENGTH : integer := 4;
    BW_WIDTH     : integer := 8;
    DATA_WIDTH   : integer := 72
    );
  port(
    clk0             : in std_logic;
    clk180           : in std_logic;
    clk270           : in std_logic;
    user_rst_0       : in std_logic;
    user_rst_180     : in std_logic;
    user_rst_270     : in std_logic;
    fifo_bw_h        : in std_logic_vector(BW_WIDTH-1 downto 0);
    fifo_bw_l        : in std_logic_vector(BW_WIDTH-1 downto 0);
    fifo_dwh         : in std_logic_vector(DATA_WIDTH-1 downto 0);
    fifo_dwl         : in std_logic_vector(DATA_WIDTH-1 downto 0);
    dummy_wr         : in std_logic_vector(1 downto 0);
    wr_init_n        : in std_logic;
    wr_init2_n       : out std_logic;
    qdr_bw_n         : out std_logic_vector(BW_WIDTH-1 downto 0);
    qdr_d            : out std_logic_vector(DATA_WIDTH-1 downto  0);
    qdr_w_n          : out std_logic;
    dummy_wrl        : out std_logic_vector(DATA_WIDTH-1 downto  0);
    dummy_wrh        : out std_logic_vector(DATA_WIDTH-1 downto  0);
    dummy_wren       : out std_logic
    );
end entity qdrii_phy_write;

architecture arch_qdrii_phy_write of qdrii_phy_write is

  constant PATTERN_A : std_logic_vector(8 downto 0) := "111111111";
  constant PATTERN_B : std_logic_vector(8 downto 0) := "000000000";
  constant PATTERN_C : std_logic_vector(8 downto 0) := "101010101";
  constant PATTERN_D : std_logic_vector(8 downto 0) := "010101010";

  constant IDLE    : std_logic_vector(5 downto 0) := "000001";
  constant WR_1    : std_logic_vector(5 downto 0) := "000010";
  constant WR_2    : std_logic_vector(5 downto 0) := "000100";
  constant WR_3    : std_logic_vector(5 downto 0) := "001000";
  constant WR_4    : std_logic_vector(5 downto 0) := "010000";
  constant WR_DONE : std_logic_vector(5 downto 0) := "100000";

  signal bwl_int            : std_logic_vector(BW_WIDTH-1 downto 0);
  signal bwh_int            : std_logic_vector(BW_WIDTH-1 downto 0);
  signal wr_init_delay_n    : std_logic;
  signal wr_init_delay2_n   : std_logic;
  signal wr_init_delay3_n   : std_logic;
  signal qdr_w_n_int        : std_logic;
  signal dummy_wr_r         : std_logic_vector(1 downto 0);
  signal dwl_int            : std_logic_vector(DATA_WIDTH-1 downto  0);
  signal dwh_int            : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal wr_cmd_in          : std_logic;
  signal wr_fifo_rden_1     : std_logic;
  signal wr_fifo_rden_2     : std_logic;
  signal wr_init2_n_1       : std_logic;
  signal wr_init2_n_i       : std_logic;
  signal d_wr_en            : std_logic;
  signal Next_datagen_st    : std_logic_vector(5 downto 0);
  signal PAT_A              : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal PAT_B              : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal PAT_C              : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal PAT_D              : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dummy_write_l      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dummy_write_h      : std_logic_vector(DATA_WIDTH-1 downto 0);

  component qdrii_phy_d_io
    port(
      clk270 : in  std_logic;
      dwl    : in  std_logic;
      dwh    : in  std_logic;
      qdr_d  : out std_logic
      );
  end component qdrii_phy_d_io;

  component qdrii_phy_bw_io
    port(
      clk270   : in  std_logic;
      bwl      : in  std_logic;
      bwh      : in  std_logic;
      qdr_bw_n : out std_logic
      );
  end component qdrii_phy_bw_io;

  attribute syn_useioff : boolean;
  attribute IOB : string;

begin

    --*****************************************************************
  -- Calibration Write data logic
  --*****************************************************************

  ASGN : for i in 0 to BW_WIDTH-1 generate
    PAT_A(((i+1)*9)-1 downto (9*i)) <= PATTERN_A;
    PAT_B(((i+1)*9)-1 downto (9*i)) <= PATTERN_B;
    PAT_C(((i+1)*9)-1 downto (9*i)) <= PATTERN_C;
    PAT_D(((i+1)*9)-1 downto (9*i)) <= PATTERN_D;
  end generate ASGN;

  -- For Calibration purpose, a sequence of pattern datas are written in to
  -- Write Data FIFOs.
  -- For BL4, a pattern of F-0, F-0, F-0, A-5 are written into Write Data FIFOs.
  -- For BL2, a pattern of F-0, F-0, A-5 are written into Write Data FIFOs.
  process(clk0)
  begin
    if(rising_edge(clk0)) then
      if (user_rst_0 = '1') then
        dummy_write_h   <= (others => '0');
        dummy_write_l   <= (others => '0');
        d_wr_en         <= '0';
        Next_datagen_st <= IDLE;
      else
        case (Next_datagen_st) is
          when IDLE =>
            dummy_write_h   <= (others => '0');
            dummy_write_l   <= (others => '0');
            d_wr_en         <= '0';
            Next_datagen_st <= WR_1;

          when WR_1 =>
            dummy_write_h   <= PAT_A;
            dummy_write_l   <= PAT_B;
            d_wr_en         <= '1';
            if(BURST_LENGTH = 4) then
              Next_datagen_st <= WR_2;
            elsif(BURST_LENGTH = 2) then
              Next_datagen_st <= WR_3;
            end if;

          when WR_2 =>

            dummy_write_h   <= PAT_A;
            dummy_write_l   <= PAT_B;
            d_wr_en         <= '0';
            Next_datagen_st <= WR_3;

          when WR_3 =>

            dummy_write_h   <= PAT_A;
            dummy_write_l   <= PAT_B;
            d_wr_en         <= '1';
            Next_datagen_st <= WR_4;

          when WR_4 =>

            dummy_write_h <= PAT_C;
            dummy_write_l <= PAT_D;
            if(BURST_LENGTH = 4) then
              d_wr_en <= '0';
            elsif(BURST_LENGTH = 2) then
              d_wr_en <= '1';
            end if;
            Next_datagen_st <= WR_DONE;

          when WR_DONE =>
            dummy_write_h   <= (others => '0');
            dummy_write_l   <= (others => '0');
            d_wr_en         <= '0';
            Next_datagen_st <= WR_DONE;

          when others =>
            dummy_write_h   <= (others => '0');
            dummy_write_l   <= (others => '0');
            d_wr_en         <= '0';
            Next_datagen_st <= IDLE;

        end case;
      end if;
    end if;
  end process;

  process (clk0)
  begin
    if(rising_edge(clk0)) then
      dummy_wrl <= dummy_write_l;
      dummy_wrh <= dummy_write_h;
      dummy_wren <= d_wr_en;
    end if;
  end process;

  -- Generate Byte Write Logic
  process (clk270)
  begin
    if(rising_edge(clk270)) then
      if (wr_init2_n_1 = '0') then
        bwh_int <= fifo_bw_h;
        bwl_int <= fifo_bw_l;
      else
        bwl_int <= (others => '0');
        bwh_int <= (others => '0');
      end if;
    end if;
  end process;

  BW_INST : for bw_i in 0 to BW_WIDTH-1 generate
    U_QDRII_PHY_BW_IO : qdrii_phy_bw_io
      port map(
        clk270   => clk270,
        bwl      => bwl_int(bw_i),
        bwh      => bwh_int(bw_i),
        qdr_bw_n => qdr_bw_n(bw_i)
        );
  end generate;

  wr_cmd_in <= not (not wr_init_n or dummy_wr(1) or dummy_wr(0));

  -- Generate Write Burst Logic
  process (clk270 )
  begin
    if(rising_edge(clk270)) then
      if (wr_init2_n_1 = '0') then
        dwh_int <= fifo_dwh;
        dwl_int <= fifo_dwl;
      else
        dwl_int <= (others => '0');
        dwh_int <= (others => '0');
      end if;
    end if;
  end process;

  ------------------------------------------------------------------------------
  -- QDR D IO instantiations
  ------------------------------------------------------------------------------

  D_INST : for d_i in 0 to DATA_WIDTH-1 generate
    U_QDRII_PHY_D_IO : qdrii_phy_d_io
      port map(
        clk270 => clk270,
        dwl    => dwl_int(d_i),
        dwh    => dwh_int(d_i),
        qdr_d  => qdr_d(d_i)
        );
  end generate;

  -- Generate write data fifo rden
  WR_FIFO_RDEN_FF1 : FDRSE
    generic map (
      INIT => '1'
      )
    port map (
      Q  => wr_fifo_rden_1,
      C  => clk270,
      CE => '1',
      D  => wr_cmd_in,
      R  => '0',
      S  => '0'
      );

  WR_FIFO_RDEN_FF2 : FDRSE
    generic map (
      INIT => '1'
      )
    port map (
      Q  => wr_fifo_rden_2,
      C  => clk270,
      CE => '1',
      D  => wr_fifo_rden_1,
      R  => '0',
      S  => '0'
      );

  -- A single Write Command is expanded for two clock cycles for BL4, so that
  -- two sets of Write Datas can be read from Write Data FIFOs. For BL2 only
  -- one set of Write Datas can be read form Write Data FIFOs.
  wr_init2_n_i <= (wr_fifo_rden_1 and wr_fifo_rden_2 ) when (BURST_LENGTH = 4) else
                   wr_fifo_rden_1;
  wr_init2_n   <= wr_init2_n_i;

  WR_INIT2_N_FF : FDRSE
    generic map (
      INIT => '0'
      )
    port map (
      Q  => wr_init2_n_1,
      C  => clk270,
      CE => '1',
      D  => wr_init2_n_i,
      R  => '0',
      S  => '0'
      );

  -- Generate QDR_W_n logic
  WR_INIT_FF1 : FDRSE
    generic map (
      INIT => '1'
      )
    port map (
      Q  => wr_init_delay_n,
      C  => clk270,
      CE => '1',
      D  => wr_cmd_in,
      R  => '0',
      S  => '0'
      );

  WR_INIT_FF2 : FDRSE
    generic map (
      INIT => '1'
      )
    port map (
      Q  => wr_init_delay2_n,
      C  => clk180,
      CE => '1',
      D  => wr_init_delay_n,
      R  => '0',
      S  => '0'
      );

  BL4_INST : if(BURST_LENGTH = 4) generate
  attribute syn_useioff of WR_INIT_FF3 : label is true;
  attribute IOB of WR_INIT_FF3 : label is "force";
  begin
    WR_INIT_FF3 : FDCPE
      generic map (
        INIT => '1'
        )
      port map (
        Q   => qdr_w_n_int,
        C   => clk180,
        CE  => '1',
        D   => wr_init_delay2_n,
        CLR => '0',
        PRE => user_rst_180
        );
  end generate;

  BL2_INST : if(BURST_LENGTH = 2) generate
  attribute syn_useioff of WR_INIT_FF4 : label is true;
  attribute IOB of WR_INIT_FF4 : label is "force";
  begin
    WR_INIT_FF3 : FDRSE
      generic map (
        INIT => '1'
        )
      port map (
        Q  => wr_init_delay3_n,
        C  => clk180,
        CE => '1',
        D  => wr_init_delay2_n,
        R  => '0',
        S  => '0'
        );

    WR_INIT_FF4 : FDCPE
      generic map (
        INIT => '1'
        )
      port map (
        Q   => qdr_w_n_int,
        C   => clk180,
        CE  => '1',
        D   => wr_init_delay3_n,
        CLR => '0',
        PRE => user_rst_180
        );
  end generate;

  QDR_W_N_OBUF : OBUF
    port map(
      I => qdr_w_n_int,
      O => qdr_w_n
      );

end architecture arch_qdrii_phy_write;