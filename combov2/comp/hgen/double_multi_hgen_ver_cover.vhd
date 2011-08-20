-- multi_hgen_ver_cover.vhd: Verification cover of HGEN
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
entity DOUBLE_MULTI_HGEN_VER_COVER is
   generic(
      -- the data width of the data input/output
      DATA_WIDTH             : integer   := 128;
      FIRST_STAGE_BRANCHES   : integer   := 8;
      SECOND_STAGE_BRANCHES  : integer   := 8
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

architecture arch of DOUBLE_MULTI_HGEN_VER_COVER is

   -- FrameLink between HGENs
   signal fl_inter_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_inter_rem         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_inter_sof_n       : std_logic;
   signal fl_inter_eof_n       : std_logic;
   signal fl_inter_sop_n       : std_logic;
   signal fl_inter_eop_n       : std_logic;
   signal fl_inter_src_rdy_n   : std_logic;
   signal fl_inter_dst_rdy_n   : std_logic;

begin

   front_hgen_multi_i: entity work.MULTI_HGEN_VER_COVER
   generic map(
      -- the data width of the data input/output
      DATA_WIDTH     => DATA_WIDTH,
      BRANCH_COUNT   => FIRST_STAGE_BRANCHES,
      USE_BRAMS_FOR_HGEN_FIFO => false
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
      TX_DATA           => fl_inter_data,
      TX_REM            => fl_inter_rem,
      TX_SRC_RDY_N      => fl_inter_src_rdy_n,
      TX_DST_RDY_N      => fl_inter_dst_rdy_n,
      TX_SOP_N          => fl_inter_sop_n,
      TX_EOP_N          => fl_inter_eop_n,
      TX_SOF_N          => fl_inter_sof_n,
      TX_EOF_N          => fl_inter_eof_n
   ); 

   back_hgen_multi_i: entity work.MULTI_HGEN_VER_COVER
   generic map(
      -- the data width of the data input/output
      DATA_WIDTH     => DATA_WIDTH,
      BRANCH_COUNT   => SECOND_STAGE_BRANCHES,
      USE_BRAMS_FOR_HGEN_FIFO => false
   )
   port map(
      -- common signals
      -- global FGPA clock
      CLK               => CLK,

      -- global synchronous reset
      RESET             => RESET,
      
      -- RX Framelink interface
      RX_DATA           => fl_inter_data,
      RX_REM            => fl_inter_rem,
      RX_SRC_RDY_N      => fl_inter_src_rdy_n,
      RX_DST_RDY_N      => fl_inter_dst_rdy_n,
      RX_SOP_N          => fl_inter_sop_n,
      RX_EOP_N          => fl_inter_eop_n,
      RX_SOF_N          => fl_inter_sof_n,
      RX_EOF_N          => fl_inter_eof_n,

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

end architecture;
