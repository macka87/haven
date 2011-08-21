-- hgen_ver_cover.vhd: Verification cover of HGEN
-- Copyright (C) 2011 Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity HGEN_VER_COVER is
   generic(
      -- the data width of the data input/output
      DATA_WIDTH     : integer   := 128
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input data interface
      RX_DATA        :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         :  in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       :  in std_logic;
      RX_EOF_N       :  in std_logic;
      RX_SOP_N       :  in std_logic;
      RX_EOP_N       :  in std_logic;
      RX_SRC_RDY_N   :  in std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- output data interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   :  in std_logic
   );

end entity;

architecture arch of HGEN_VER_COVER is

   -- constants
   constant HGEN_UH_SIZE : integer := 64;

   constant HGEN_DATA_WIDTH : integer := 128;

   -- signals
   signal hgen_mask      : std_logic_vector(HGEN_UH_SIZE-1 downto 0);

   signal mi_dwr         : std_logic_vector(31 downto 0);
   signal mi_addr        : std_logic_vector(31 downto 0);
   signal mi_wr          : std_logic;
   signal mi_rd          : std_logic;
   signal mi_be          : std_logic_vector(3 downto 0);

   -- input transformer signals
   signal in_trans_tx_data       : std_logic_vector(HGEN_DATA_WIDTH-1 downto 0);
   signal in_trans_tx_rem        : std_logic_vector(log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal in_trans_tx_sof_n      : std_logic;
   signal in_trans_tx_sop_n      : std_logic;
   signal in_trans_tx_eop_n      : std_logic;
   signal in_trans_tx_eof_n      : std_logic;
   signal in_trans_tx_src_rdy_n  : std_logic;
   signal in_trans_tx_dst_rdy_n  : std_logic;

   -- output transformer signals
   signal out_trans_rx_data      : std_logic_vector(HGEN_DATA_WIDTH-1 downto 0);
   signal out_trans_rx_rem       : std_logic_vector(log2(HGEN_DATA_WIDTH/8)-1 downto 0);
   signal out_trans_rx_sof_n     : std_logic;
   signal out_trans_rx_sop_n     : std_logic;
   signal out_trans_rx_eop_n     : std_logic;
   signal out_trans_rx_eof_n     : std_logic;
   signal out_trans_rx_src_rdy_n : std_logic;
   signal out_trans_rx_dst_rdy_n : std_logic;

begin

   -- input transformer
   input_trans_i: entity work.FL_TRANSFORMER
   generic map(
      -- the data width of the data input
      RX_DATA_WIDTH  => DATA_WIDTH,
      TX_DATA_WIDTH  => HGEN_DATA_WIDTH
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,

      -- RX Framelink interface
      RX_DATA           => RX_DATA,
      RX_REM            => RX_REM,
      RX_SOP_N          => RX_SOP_N,
      RX_EOP_N          => RX_EOP_N,
      RX_SOF_N          => RX_SOF_N,
      RX_EOF_N          => RX_EOF_N,
      RX_SRC_RDY_N      => RX_SRC_RDY_N,
      RX_DST_RDY_N      => RX_DST_RDY_N,

      -- TX FrameLink interface
      TX_DATA           => in_trans_tx_data,
      TX_REM            => in_trans_tx_rem,
      TX_SOP_N          => in_trans_tx_sop_n,
      TX_EOP_N          => in_trans_tx_eop_n,
      TX_SOF_N          => in_trans_tx_sof_n,
      TX_EOF_N          => in_trans_tx_eof_n,
      TX_SRC_RDY_N      => in_trans_tx_src_rdy_n,
      TX_DST_RDY_N      => in_trans_tx_dst_rdy_n
   );

   -- HGEN
   hgen_i: entity work.HGEN
   generic map(
      -- the data width of the data input/output
      DATA_WIDTH     => HGEN_DATA_WIDTH,
      -- defines UH size in bytes; min 16 - 128 bytes
      UH_SIZE        => HGEN_UH_SIZE
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,

      -- RX Framelink interface
      RX_DATA           => in_trans_tx_data,
      RX_REM            => in_trans_tx_rem,
      RX_SOP_N          => in_trans_tx_sop_n,
      RX_EOP_N          => in_trans_tx_eop_n,
      RX_SOF_N          => in_trans_tx_sof_n,
      RX_EOF_N          => in_trans_tx_eof_n,
      RX_SRC_RDY_N      => in_trans_tx_src_rdy_n,
      RX_DST_RDY_N      => in_trans_tx_dst_rdy_n,

      -- TX FrameLink interface
      TX_DATA           => out_trans_rx_data,
      TX_REM            => out_trans_rx_rem,
      TX_SOP_N          => out_trans_rx_sop_n,
      TX_EOP_N          => out_trans_rx_eop_n,
      TX_SOF_N          => out_trans_rx_sof_n,
      TX_EOF_N          => out_trans_rx_eof_n,
      TX_SRC_RDY_N      => out_trans_rx_src_rdy_n,
      TX_DST_RDY_N      => out_trans_rx_dst_rdy_n,

      -- SW memory interface
      MI_DWR            => mi_dwr,
      MI_ADDR           => mi_addr,
      MI_RD             => mi_rd,
      MI_WR             => mi_wr,
      MI_BE             => mi_be,
      MI_DRD            => open,
      MI_ARDY           => open,
      MI_DRDY           => open,

      -- Masking input, typically constant
      MASK              => hgen_mask
   );

   -- output transformer
   output_trans_i: entity work.FL_TRANSFORMER
   generic map(
      -- the data width of the data input
      RX_DATA_WIDTH  => HGEN_DATA_WIDTH,
      TX_DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,

      -- RX Framelink interface
      RX_DATA           => out_trans_rx_data,
      RX_REM            => out_trans_rx_rem,
      RX_SOP_N          => out_trans_rx_sop_n,
      RX_EOP_N          => out_trans_rx_eop_n,
      RX_SOF_N          => out_trans_rx_sof_n,
      RX_EOF_N          => out_trans_rx_eof_n,
      RX_SRC_RDY_N      => out_trans_rx_src_rdy_n,
      RX_DST_RDY_N      => out_trans_rx_dst_rdy_n,

      -- TX FrameLink interface
      TX_DATA           => TX_DATA,
      TX_REM            => TX_REM,
      TX_SOP_N          => TX_SOP_N,
      TX_EOP_N          => TX_EOP_N,
      TX_SOF_N          => TX_SOF_N,
      TX_EOF_N          => TX_EOF_N,
      TX_SRC_RDY_N      => TX_SRC_RDY_N,
      TX_DST_RDY_N      => TX_DST_RDY_N
   );

   mi_dwr <= "10100101101001000101110111010111";
   mi_addr <= (others => '0');
   mi_wr <= '1';
   mi_rd <= '0';
   mi_be <= "1111";

   hgen_mask <= (others => '1');

end architecture;
