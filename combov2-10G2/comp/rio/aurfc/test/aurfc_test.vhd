
-- aurfc_test.vhd: Aurfc test component 
-- Copyright (C) 2007 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the OpenIPCore Hardware General Public
-- License as published by the OpenIPCore Organization; either version
-- 0.20-15092000 of the License, or (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- OpenIPCore Hardware General Public License for more details.
--
-- You should have received a copy of the OpenIPCore Hardware Public
-- License along with this program; if not, download it from
-- OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
--
-- $Id$
-- 
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all;
use WORK.bmem_func.all;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity aurfc_test is
   generic (
      BASE_ADDR         : integer := 0;
      
      LANES             : integer;                 -- Number of lanes 
      DATA_PATHS        : integer;                 -- Number of data paths
      
      LOOPBACK : std_logic_vector := "00"
      );
   port (
      RESET    : in std_logic;
      REFCLK   : in std_logic;
      USRCLK  : in std_logic;
      USRCLK2 : in std_logic;
      CMDCLK   : in std_logic;
      
      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0);
      
      -- Local Bus Interface
      LBCLK     : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME   : in    std_logic;  -- Frame
      LBHOLDA   : out   std_logic;  -- Hold Ack
      LBAD      : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS      : in    std_logic;  -- Adress strobe
      LBRW      : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY     : out   std_logic;  -- Ready
      LBLAST    : in    std_logic   -- Last word in transfer
   );
end aurfc_test;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of aurfc_test is

constant ADDR_WIDTH  : integer := 15;
constant MEM_DATA_WIDTH  : integer := 73;
constant ITEMS       : integer := 512;

component aurfc is
   generic (
      LANES             : integer;                 -- Number of lanes 
      DATA_PATHS        : integer;                 -- Number of data paths
      DISCARD_BAD_PACKETS : boolean := false;

      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true;
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 3;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 3;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no DCMs, insert BUFG buffer!)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- LocalLink TX Interface
      TX_D             : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      TX_REM           : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      TX_SRC_RDY_N     : in std_logic;
      TX_SOF_N         : in std_logic;
      TX_SOP_N         : in std_logic;
      TX_EOF_N         : in std_logic;
      TX_EOP_N         : in std_logic;
      TX_DST_RDY_N     : out std_logic;

      -- LocalLink RX Interface
      RX_D             : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_REM           : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      RX_SRC_RDY_N     : out std_logic;
      RX_SOF_N         : out std_logic;
      RX_SOP_N         : out std_logic;
      RX_EOF_N         : out std_logic;
      RX_EOP_N         : out std_logic;
      RX_DST_RDY_N     : in std_logic;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- Status Interface
      TX_STATUS      : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0);   -- TX fifo status
      RX_STATUS      : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);   -- RX fifo status
      CHANNEL_UP     : out std_logic;                                      -- Aurora Channel Status (0: channel down, 1: channel up)

      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);
      D_CNT_XON   : out std_logic_vector(31 downto 0);
      D_CNT_XOFF  : out std_logic_vector(31 downto 0);
      D_RX_FULL      : out std_logic_vector(15 downto 0);

      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0)
   );
end component;

   -- address decoder signals
   signal lb_en               : std_logic;
   signal lb_rw               : std_logic;
   signal lb_drdy             : std_logic;
   signal lb_addr             : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal lb_di               : std_logic_vector(15 downto 0);
   signal lb_do               : std_logic_vector(15 downto 0);

   signal adc_rd              : std_logic;
   signal adc_wr              : std_logic;
   signal adc_addr            : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal reg_adc_addr        : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal reg_adc_addr_p1     : std_logic_vector(ADDR_WIDTH-2 downto 0);
   signal adc_do              : std_logic_vector(31 downto 0);
   signal adc_di              : std_logic_vector(31 downto 0);
   signal adc_drdy            : std_logic;

   signal controls_do         : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_adc_do_i        : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_adc_do          : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_adc_di          : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_adc_di_z        : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_adc_drdy_i      : std_logic;
   signal reg_adc_drdy        : std_logic;
   signal reg_controls_drdy : std_logic;

   signal reg_tx_active : std_logic;
   signal null_sig      : std_logic_vector(95 downto MEM_DATA_WIDTH);
   signal null_sig2     : std_logic_vector(MEM_DATA_WIDTH-1 downto 9);
   signal null_sig3     : std_logic_vector(MEM_DATA_WIDTH-1 downto 64);

   signal cs_tx_mem : std_logic;
   signal cs_ctrl_mem : std_logic;
   signal cs_recv_mem : std_logic;
   signal cs_corr_mem : std_logic;
   signal cs_controls : std_logic;
   signal cs_reg_tx_active : std_logic;
   signal cs_cnt_err  : std_logic;
   signal cs_debug_reg: std_logic;

   signal gnd_bus    : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);

   signal cnt_tx_addr : std_logic_vector(8 downto 0);
   signal cnt_rx_addr : std_logic_vector(8 downto 0);
   signal cnt_err_addr : std_logic_vector(8 downto 0);

   signal tx_mem_rea : std_logic;
   signal tx_mem_wea : std_logic;
   signal tx_mem_doa : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal tx_mem_doa_dv : std_logic;
   signal tx_mem_pipe_enb : std_logic;
   signal tx_mem_reb : std_logic;
   signal tx_mem_dob_dv : std_logic;
   signal tx_mem_dob : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);

   signal ctrl_mem_rea : std_logic;
   signal ctrl_mem_wea : std_logic;
   signal ctrl_mem_doa : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal ctrl_mem_doa_dv : std_logic;
   signal ctrl_mem_pipe_enb : std_logic;
   signal ctrl_mem_reb : std_logic;
   signal ctrl_mem_dob_dv : std_logic;
   signal ctrl_mem_dob : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);

   signal corr_mem_rea : std_logic;
   signal corr_mem_doa : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal corr_mem_doa_dv : std_logic;
   signal corr_mem_web : std_logic;

   signal recv_mem_rea : std_logic;
   signal recv_mem_doa : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal recv_mem_doa_dv : std_logic;
   signal recv_mem_web : std_logic;

   signal tx_d       : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal tx_rem        : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal tx_src_rdy_n     : std_logic;
   signal tx_sof_n         : std_logic;
   signal tx_sop_n         : std_logic;
   signal tx_eof_n         : std_logic;
   signal tx_eop_n         : std_logic;
   signal tx_dst_rdy_n     : std_logic;

   signal rx_d       : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal rx_rem        : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal rx_src_rdy_n     : std_logic;
   signal rx_sof_n         : std_logic;
   signal rx_sop_n         : std_logic;
   signal rx_eof_n         : std_logic;
   signal rx_eop_n         : std_logic;
   signal rx_dst_rdy_n     : std_logic;

   signal rx_d_z     : std_logic_vector(63 downto 0);
   signal rx_rem_z   : std_logic_vector(2 downto 0);

   signal hard_error       : std_logic;
   signal soft_error       : std_logic;
   signal frame_error      : std_logic;

   signal tx_status        : std_logic_vector(2 downto 0);
   signal rx_status        : std_logic_vector(2 downto 0);
   signal channel_up       : std_logic;

   signal rx_d_valid       : std_logic;
   signal reg_rx_d_p1      : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_rx_d         : std_logic_vector(MEM_DATA_WIDTH-1 downto 0);
   signal reg_rx_d_valid_p1: std_logic;
   signal reg_rx_d_valid   : std_logic;
   signal cmp_bad_data     : std_logic;
   signal cmp_bad_data_noeop  : std_logic;
   signal cmp_bad_data_eop  : std_logic;
   signal reg_rx_eop_n_p1  : std_logic;
   signal reg_rx_eop_n     : std_logic;
   signal cnt_hard_error : std_logic_vector(15 downto 0);
   signal cnt_soft_error : std_logic_vector(15 downto 0);
   signal cnt_frame_error : std_logic_vector(15 downto 0);
   signal cnt_rx_dst_rdy : std_logic_vector(3 downto 0);
   signal cnt_rx_dst_rdy_ovf : std_logic;

   -- debug
   signal d_aurfc_state    : std_logic_vector(1 downto 0);
   signal d_cnt_xon        : std_logic_vector(31 downto 0);
   signal d_cnt_xoff       : std_logic_vector(31 downto 0);
   signal debug_status     : std_logic_vector(63 downto 0);
   signal d_rx_full        : std_logic_vector(15 downto 0);
   signal reg_debug        : std_logic_vector(63 downto 0);
   signal reg_eof_n : std_logic;
   
begin

gnd_bus <= (others => '0');

-- -------------------------------------------------------------
-- LBCONNMEM instantion

LB_CONNECTION : entity work.lbconn_mem
generic map(
   ADDR_WIDTH     => ADDR_WIDTH, -- address bus width
   BASE           => BASE_ADDR,       -- base address
   USE_HIGH_LOGIC => FALSE
)
port map(
   data_out => lb_di,
   data_in  => lb_do,
   addr     => lb_addr,
   en       => lb_en,
   rw       => lb_rw,
   sel      => open,
   drdy     => lb_drdy,
   ardy     => '1',
   reset    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

-- -------------------------------------------------------------
-- ADC2LB component instantion

ADC2LB_U : entity work.adc2lb
generic map(
   ADDR_WIDTH  => ADDR_WIDTH,
   FREQUENCY   => 100
)
port map(
   RESET       => RESET,

   -- Address decoder interface
   CLK         => LBCLK,
   ADC_RD      => adc_rd,
   ADC_WR      => adc_wr,
   ADC_ADDR    => adc_addr,
   ADC_DI      => adc_di,
   ADC_DO      => adc_do,
   ADC_DRDY    => adc_drdy,

   -- Local Bus interface
   LBCLK       => LBCLK,
   LB_EN       => lb_en,
   LB_RW       => lb_rw,
   LB_ADDR     => lb_addr,
   LB_DI       => lb_di,
   LB_DO       => lb_do,
   LB_DRDY     => lb_drdy
);

-- -------------------------------------------------------------
-- Address decoder

-- thing    - sw addr   (adc_addr)
-- -------------------------------
-- tx_mem   - 0000-1800 (0000-0600)
-- ctrl_mem - 2000-3800 (0800-0e00)
-- recv_mem - 4000-5800 (1000-1600)
-- corr_mem - 6000-7800 (1800-1e00)
-- controls - 8000-ffff (2000-3fff)
-- 
-- controls item - sw offset  (adc offset)
-- ---------------------------------------
-- reg_tx_active - 00         (00)
-- cnt_err       - 10         (04)
-- debug_reg     - 20-30      (08-0C)

process(RESET, LBCLK)
begin
 if (RESET = '1') then
    reg_adc_addr_p1  <= (others => '0');
    reg_adc_addr     <= (others => '0');
 elsif (LBCLK'event AND LBCLK = '1') then
    reg_adc_addr_p1 <= adc_addr;
    reg_adc_addr <= reg_adc_addr_p1;
 end if;
end process;
   
cs_tx_mem   <= '1' when adc_addr(13 downto 11) = "000" else '0';
cs_ctrl_mem <= '1' when adc_addr(13 downto 11) = "001" else '0';
cs_recv_mem <= '1' when adc_addr(13 downto 11) = "010" else '0';
cs_corr_mem <= '1' when adc_addr(13 downto 11) = "011" else '0';
cs_controls <= '1' when adc_addr(13 downto 11) = "100" else '0';

-- -------------------------------------------------------------
-- TX_MEM

-- what           - bits
-- --------------------------------------------
-- tx_d           - ((DATA_PATHS*8)-1 downto 0)
-- tx_rem         - (66 downto 64);
-- tx_src_rdy_n   - not(72);
-- tx_sof_n       - not(71)
-- tx_sop_n       - not(70)
-- tx_eop_n       - not(69)
-- tx_eof_n       - not(68)

tx_mem_wea <= cs_tx_mem and adc_wr;
tx_mem_rea <= cs_tx_mem and adc_rd;

tx_mem : entity work.dp_bmem
   generic map(
      BRAM_TYPE   => 36,
      DATA_WIDTH  => MEM_DATA_WIDTH,
      ITEMS       => ITEMS,
      OUTPUT_REG  => TRUE
   )
   port map(
      RESET       => RESET,

      CLKA        => LBCLK,
      PIPE_ENA    => '1',
      REA         => tx_mem_rea,
      WEA         => tx_mem_wea,
      ADDRA       => adc_addr(10 downto 2),
      DIA         => reg_adc_di,
      DOA         => tx_mem_doa,
      DOA_DV      => tx_mem_doa_dv,

      CLKB        => CMDCLK,
      PIPE_ENB    => tx_mem_pipe_enb,
      REB         => tx_mem_reb,
      WEB         => '0',
      ADDRB       => cnt_tx_addr,
      DIB         => gnd_bus,
      DOB_DV      => tx_mem_dob_dv,
      DOB         => tx_mem_dob
   );

-- -------------------------------------------------------------
-- CTRL_MEM
ctrl_mem_wea <= cs_ctrl_mem and adc_wr;
ctrl_mem_rea <= cs_ctrl_mem and adc_rd;

ctrl_mem : entity work.dp_bmem
   generic map(
      BRAM_TYPE   => 36,
      DATA_WIDTH  => MEM_DATA_WIDTH,
      ITEMS       => ITEMS,
      OUTPUT_REG  => TRUE
   )
   port map(
      RESET       => RESET,

      CLKA        => LBCLK,
      PIPE_ENA    => '1',
      REA         => ctrl_mem_rea,
      WEA         => ctrl_mem_wea,
      ADDRA       => adc_addr(10 downto 2),
      DIA         => reg_adc_di_z,
      DOA         => ctrl_mem_doa,
      DOA_DV      => ctrl_mem_doa_dv,

      CLKB        => CMDCLK,
      PIPE_ENB    => ctrl_mem_pipe_enb,
      REB         => ctrl_mem_reb,
      WEB         => '0',
      ADDRB       => cnt_rx_addr,
      DIB         => gnd_bus,
      DOB_DV      => ctrl_mem_dob_dv,
      DOB         => ctrl_mem_dob
   );

-- -------------------------------------------------------------
-- RECV_MEM
recv_mem_rea <= cs_recv_mem and adc_rd;

recv_mem : entity work.dp_bmem
   generic map(
      BRAM_TYPE   => 36,
      DATA_WIDTH  => MEM_DATA_WIDTH,
      ITEMS       => ITEMS,
      OUTPUT_REG  => TRUE
   )
   port map(
      RESET       => RESET,

      CLKA        => LBCLK,
      PIPE_ENA    => '1',
      REA         => recv_mem_rea,
      WEA         => '0',
      ADDRA       => adc_addr(10 downto 2),
      DIA         => reg_adc_di,
      DOA         => recv_mem_doa,
      DOA_DV      => recv_mem_doa_dv,

      CLKB        => CMDCLK,
      PIPE_ENB    => '1',
      REB         => '0',
      WEB         => recv_mem_web,
      ADDRB       => cnt_err_addr,
      DIB         => reg_rx_d,
      DOB_DV      => open,
      DOB         => open
   );

-- -------------------------------------------------------------
-- CORR_MEM
corr_mem_rea <= cs_corr_mem and adc_rd;

corr_mem : entity work.dp_bmem
   generic map(
      BRAM_TYPE   => 36,
      DATA_WIDTH  => MEM_DATA_WIDTH,
      ITEMS       => ITEMS,
      OUTPUT_REG  => TRUE
   )
   port map(
      RESET       => RESET,

      CLKA        => LBCLK,
      PIPE_ENA    => '1',
      REA         => corr_mem_rea,
      WEA         => '0',
      ADDRA       => adc_addr(10 downto 2),
      DIA         => reg_adc_di,
      DOA         => corr_mem_doa,
      DOA_DV      => corr_mem_doa_dv,

      CLKB        => CMDCLK,
      PIPE_ENB    => '1',
      REB         => '0',
      WEB         => corr_mem_web,
      ADDRB       => cnt_err_addr,
      DIB         => ctrl_mem_dob,
      DOB_DV      => open,
      DOB         => open
   );

-- -------------------------------------------------------------
-- Input data mux

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_adc_di <= (others => '0');
   elsif (LBCLK'event AND LBCLK = '1') then
      if (adc_wr = '1') then
         if (adc_addr(1 downto 0) = "00") then
            reg_adc_di(31 downto 0) <= adc_di;
         elsif (adc_addr(1 downto 0) = "01") then
            reg_adc_di(63 downto 32) <= adc_di;
         elsif (adc_addr(1 downto 0) = "10") then
            reg_adc_di(MEM_DATA_WIDTH-1 downto 64) <= adc_di(31-(95-MEM_DATA_WIDTH)-1 downto 0);
         end if;
      end if;
   end if;
end process;

reg_adc_di_z_gen: for i in 0 to MEM_DATA_WIDTH-1 generate
   i_lt_datawidth_gen: if (i < (DATA_PATHS*8)) generate
      reg_adc_di_z(i) <= reg_adc_di(i);
   end generate;
   i_ge_datawidth_gen: if ((i >= (DATA_PATHS*8)) and (i < 64)) generate
      reg_adc_di_z(i) <= '0';
   end generate;
   i_ge_64_gen: if ((i >= 64) and (i < (log2(DATA_PATHS)+64))) generate
      reg_adc_di_z(i) <= reg_adc_di(i);
   end generate;
   i_ge_log2_gen: if ((i >= (log2(DATA_PATHS)+64)) and (i < 68)) generate
      reg_adc_di_z(i) <= '0';
   end generate;
   i_ge_68_gen: if (i >= 68) generate
      reg_adc_di_z(i) <= reg_adc_di(i);
   end generate;
end generate;


-- -------------------------------------------------------------
-- Output data mux
reg_adc_do_i <= tx_mem_doa   when cs_tx_mem = '1' else
                ctrl_mem_doa when cs_ctrl_mem = '1' else
                recv_mem_doa when cs_recv_mem = '1' else
                corr_mem_doa when cs_corr_mem = '1' else
                controls_do;

reg_adc_drdy_i <= tx_mem_doa_dv   when cs_tx_mem = '1' else
                  ctrl_mem_doa_dv when cs_ctrl_mem = '1' else
                  recv_mem_doa_dv when cs_recv_mem = '1' else
                  corr_mem_doa_dv when cs_corr_mem = '1' else
                  reg_controls_drdy;

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_adc_do <= (others => '0');
      reg_adc_drdy <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_adc_do <= reg_adc_do_i;
      reg_adc_drdy <= reg_adc_drdy_i;
   end if;
end process;

adc_do <= reg_adc_do(31 downto 0) when reg_adc_addr(1 downto 0) = "00" else
          reg_adc_do(63 downto 32) when reg_adc_addr(1 downto 0) = "01" else
          null_sig & reg_adc_do(MEM_DATA_WIDTH-1 downto 64) when reg_adc_addr(1 downto 0) = "10" else
          X"00000000";

null_sig <= (others => '0');
null_sig2 <= (others => '0');
null_sig3 <= (others => '0');

adc_drdy <= reg_adc_drdy;

-- Output data mux
controls_do <= null_sig3 & cnt_hard_error & cnt_soft_error & cnt_frame_error & 
               x"000" & "00" & channel_up & reg_tx_active when cs_reg_tx_active = '1' else
               null_sig2 & cnt_err_addr when cs_cnt_err = '1' else
               null_sig3 & reg_debug when cs_debug_reg = '1' else
               (others => '0');

-- -------------------------------------------------------------
-- Control logic

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_controls_drdy <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      reg_controls_drdy <= adc_rd;
   end if;
end process;

-- Controls address decoder
cs_reg_tx_active <= '1' when cs_controls = '1' and adc_addr(4 downto 2) = "000" else '0';
cs_cnt_err       <= '1' when cs_controls = '1' and adc_addr(4 downto 2) = "001" else '0';
cs_debug_reg     <= '1' when cs_controls = '1' and adc_addr(4 downto 2) = "010" else '0';

process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_tx_active <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      if (cs_reg_tx_active = '1' and adc_wr = '1') then
         reg_tx_active <= adc_di(0);
      end if;
   end if;
end process;

-- cnt_tx_addr counter : 
process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      cnt_tx_addr <= (others => '0');
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (reg_tx_active = '1' and tx_dst_rdy_n = '0') then
         cnt_tx_addr <= cnt_tx_addr + 1;
      end if;
   end if;
end process;

rx_d_valid <= not(rx_src_rdy_n or rx_dst_rdy_n);

-- cnt_rx_addr counter : 
process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      cnt_rx_addr <= (others => '0');
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (rx_d_valid = '1') then
         cnt_rx_addr <= cnt_rx_addr + 1;
      end if;
   end if;
end process;

-- cnt_err_addr counter : 
process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      cnt_err_addr <= (others => '0');
   elsif (CMDCLK'event AND CMDCLK = '1') then
      if (cmp_bad_data = '1' and cnt_err_addr /= "111111111") then
         cnt_err_addr <= cnt_err_addr + 1;
      end if;
   end if;
end process;

process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         reg_debug <= (others => '0');
      else
         reg_debug <= debug_status;
      end if;
   end if;
end process;

debug_status <= X"DD" & "00" & d_rx_full(15 downto 0) & tx_status & rx_status 
   & d_cnt_xon(11 downto 0) & d_cnt_xoff(11 downto 0) 
   & d_aurfc_state & tx_dst_rdy_n & tx_src_rdy_n
   & d_aurfc_state & rx_dst_rdy_n & rx_src_rdy_n;


-- -------------------------------------------------------------
-- Error detection logic

rx_rem_z_gen: for i in 0 to 2 generate
   i_lt_log_gen: if (i < log2(DATA_PATHS)) generate
      rx_rem_z(i) <= rx_rem(i);
   end generate;
   i_ge_log_gen: if (i >= log2(DATA_PATHS)) generate
      rx_rem_z(i) <= '0';
   end generate;
end generate;

rx_d_z_gen: for i in 0 to 63 generate
   i_lt_datawidth_gen: if (i < (DATA_PATHS*8)) generate
      rx_d_z(i) <= rx_d(i);
   end generate;
   i_ge_datawidth_gen: if (i >= (DATA_PATHS*8)) generate
      rx_d_z(i) <= '0';
   end generate;
end generate;

process(RESET, CMDCLK)
begin
   if (RESET = '1') then
      reg_rx_d_p1 <= (others => '0');
      reg_rx_d <= (others => '0');
      reg_rx_d_valid_p1 <= '0';
      reg_rx_d_valid <= '0';
      reg_rx_eop_n_p1 <= '1';
      reg_rx_eop_n <= '1';
   elsif (CMDCLK'event AND CMDCLK = '1') then
      reg_rx_d_p1 <= "1" & (not rx_sof_n) & (not rx_sop_n) & (not rx_eop_n) & (not rx_eof_n) & "0" & rx_rem_z & rx_d_z;
      reg_rx_d <= reg_rx_d_p1;
      reg_rx_d_valid_p1 <= rx_d_valid;
      reg_rx_d_valid <= reg_rx_d_valid_p1;
      reg_rx_eop_n_p1 <= rx_eop_n;
      reg_rx_eop_n <= reg_rx_eop_n_p1;
   end if;
end process;

cmp_bad_data <= cmp_bad_data_noeop when reg_rx_eop_n = '1' else
                cmp_bad_data_eop when reg_rx_eop_n = '0' else
                '0';

cmp_bad_data_noeop <= '1' when ((reg_rx_d(63 downto 0) /= ctrl_mem_dob(63 downto 0)) or 
                               (reg_rx_d(MEM_DATA_WIDTH-1 downto 68) /= ctrl_mem_dob(MEM_DATA_WIDTH-1 downto 68))) and
                               (reg_rx_d_valid = '1') else
                      '0';
cmp_bad_data_eop <= '1' when (reg_rx_d /= ctrl_mem_dob) and reg_rx_d_valid = '1' else
                    '0';

recv_mem_web <= cmp_bad_data;
corr_mem_web <= cmp_bad_data;

-- -------------------------------------------------------------
-- AUFRC

-- data format:
-- 72       71    70    69    68    67-64 63-0
-- SRC_RDY  SOF   SOP   EOP   EOF   REM   DATA
tx_d <= tx_mem_dob((DATA_PATHS*8)-1 downto 0);
tx_rem <= tx_mem_dob(log2(DATA_PATHS)+64-1 downto 64);
tx_src_rdy_n <= not (tx_mem_dob_dv and reg_tx_active and tx_mem_dob(72));
tx_sof_n <= not tx_mem_dob(71);
tx_sop_n <= not tx_mem_dob(70);
tx_eop_n <= not tx_mem_dob(69);
tx_eof_n <= not tx_mem_dob(68);
tx_mem_reb      <= (not tx_dst_rdy_n) and reg_tx_active;
tx_mem_pipe_enb <= (not tx_dst_rdy_n) and reg_tx_active;

ctrl_mem_reb      <= rx_d_valid;
ctrl_mem_pipe_enb <= '1'; -- rx_d_valid;

-- rx_dst_rdy_n generator
rx_dst_rdy_n <= not cnt_rx_dst_rdy_ovf;
cnt_rx_dst_rdy_ovf <= '1' when cnt_rx_dst_rdy = X"F" else
                      '0';

process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         reg_eof_n <= '0';
      else
         reg_eof_n <= rx_eof_n;
      end if;
   end if;
end process;

process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         cnt_rx_dst_rdy <= (others => '0');
      elsif (rx_eof_n = '1' and reg_eof_n = '0') then
         cnt_rx_dst_rdy <= X"4";
      elsif (cnt_rx_dst_rdy_ovf = '1') then
         cnt_rx_dst_rdy <= X"C";
      else
         cnt_rx_dst_rdy <= cnt_rx_dst_rdy + 1;
      end if;
   end if;
end process;

aurfc_u: aurfc
   generic map(
      LANES             => LANES,
      DATA_PATHS        => DATA_PATHS,
      DISCARD_BAD_PACKETS => false,

      RX_IS_HEADER      => true,
      RX_IS_FOOTER      => false,
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     => 512,
      TX_STATUS_WIDTH   => 3,
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     => 512,
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   => 3,
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         => "101",
      XOFF_LIMIT        => "110",
      -- "00"=> --,
      LOOPBACK   => LOOPBACK
   )
   port map(
      -- Common Input
      RESET          => RESET,
      REFCLK         => REFCLK,
      USRCLK         => USRCLK,
      USRCLK2        => USRCLK2,
      CMDCLK         => CMDCLK,
      
      -- LocalLink TX Interface
      TX_D             => tx_d,
      TX_REM           => tx_rem,
      TX_SRC_RDY_N     => tx_src_rdy_n,
      TX_SOF_N         => tx_sof_n,
      TX_SOP_N         => tx_sop_n,
      TX_EOF_N         => tx_eof_n,
      TX_EOP_N         => tx_eop_n,
      TX_DST_RDY_N     => tx_dst_rdy_n,

      -- LocalLink RX Interface
      RX_D             => rx_d,
      RX_REM           => rx_rem,
      RX_SRC_RDY_N     => rx_src_rdy_n,
      RX_SOF_N         => rx_sof_n,
      RX_SOP_N         => rx_sop_n,
      RX_EOF_N         => rx_eof_n,
      RX_EOP_N         => rx_eop_n,
      RX_DST_RDY_N     => rx_dst_rdy_n,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => hard_error,
      SOFT_ERROR     => soft_error,
      FRAME_ERROR    => frame_error,

      -- Status Interface
      TX_STATUS      => tx_status,
      RX_STATUS      => rx_status,
      CHANNEL_UP     => channel_up,

      -- Debug
      D_STATE        => d_aurfc_state,
      D_CNT_XON      => d_cnt_xon,
      D_CNT_XOFF     => d_cnt_xoff,
      D_RX_FULL      => d_rx_full,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

-- cnt_hard_error counter : 
process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         cnt_hard_error <= (2 => '1', others => '0');
      elsif (hard_error='1') then
         cnt_hard_error <= cnt_hard_error + 1;
      end if;
   end if;
end process;

-- cnt_soft_error counter : 
process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         cnt_soft_error <= (1 => '1', others => '0');
      elsif (soft_error='1') then
         cnt_soft_error <= cnt_soft_error + 1;
      end if;
   end if;
end process;

-- cnt_frame_error counter : 
process(CMDCLK)
begin
   if (CMDCLK'event and CMDCLK = '1') then
      if (RESET = '1') then
         cnt_frame_error <= (0 => '1', others => '0');
      elsif (frame_error='1') then
         cnt_frame_error <= cnt_frame_error + 1;
      end if;
   end if;
end process;

end behavioral;





