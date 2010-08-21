-- netcope_ics.vhd : NetCOPE infrastructure
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
--
-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
use work.combov2_nc_const.all;
use work.ib_ifc_pkg.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on


-- ----------------------------------------------------------------------------
-- see /trac/netcope/wiki/NetCOPE_gics_structure
--
--              PCI_IB
--                || 
--              Switch0
--             //    \\
--          Trans0    USER_IB64
--            ||
--          Endp0
--            ||
--          Split0 === USER_MI32
--            ||
--          Split1 === to IFC and LSC connectors
--            ||
--          Split2
--       // ||  || \\
--  Split3 PipePipe \\
--  //  \\  ||  ||   \\
-- MI   MI  MI  MI    MI
-- ID  I2C  DMA TSU   NET
-- 
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture structural of netcope_ics is
   
   -- Chipscope ICON
   component icon3 is
      port (
         CONTROL0 : inout std_logic_vector(35 downto 0);
         CONTROL1 : inout std_logic_vector(35 downto 0);
         CONTROL2 : inout std_logic_vector(35 downto 0)
      );
   end component;
   
   -- Chipscope ILA (144-bit trigger port)
   component ila144 is
      port (
         CONTROL : inout std_logic_vector(35 downto 0);
         CLK     : in std_logic;
         TRIG0   : in std_logic_vector(143 downto 0)
      );
   end component;
   
   -- Chipscope ILA (72-bit trigger port)
   component ila72 is
      port (
         CONTROL : inout std_logic_vector(35 downto 0);
         CLK     : in std_logic;
         TRIG0   : in std_logic_vector(71 downto 0)
      );
   end component;
   
   -- ------------------ Signals declaration ----------------------------------
   
   -- Internal Bus 0 (ICS to GICS converter <-> Switch0)
   signal ib0_down_data      : std_logic_vector(63 downto 0);
   signal ib0_down_sof_n     : std_logic;
   signal ib0_down_eof_n     : std_logic;
   signal ib0_down_src_rdy_n : std_logic;
   signal ib0_down_dst_rdy_n : std_logic;
   signal ib0_up_data        : std_logic_vector(63 downto 0);
   signal ib0_up_sof_n       : std_logic;
   signal ib0_up_eof_n       : std_logic;
   signal ib0_up_src_rdy_n   : std_logic;
   signal ib0_up_dst_rdy_n   : std_logic;
   
   -- Internal Bus 1 (Switch0 <-> Transformer0)
   signal ib1_down_data      : std_logic_vector(63 downto 0);
   signal ib1_down_sof_n     : std_logic;
   signal ib1_down_eof_n     : std_logic;
   signal ib1_down_src_rdy_n : std_logic;
   signal ib1_down_dst_rdy_n : std_logic;
   signal ib1_up_data        : std_logic_vector(63 downto 0);
   signal ib1_up_sof_n       : std_logic;
   signal ib1_up_eof_n       : std_logic;
   signal ib1_up_src_rdy_n   : std_logic;
   signal ib1_up_dst_rdy_n   : std_logic;
   
   -- Internal Bus 2 (Transformer0 <-> Endpoint0)
   signal ib2_down_data      : std_logic_vector(31 downto 0);
   signal ib2_down_sof_n     : std_logic;
   signal ib2_down_eof_n     : std_logic;
   signal ib2_down_src_rdy_n : std_logic;
   signal ib2_down_dst_rdy_n : std_logic;
   signal ib2_up_data        : std_logic_vector(31 downto 0);
   signal ib2_up_sof_n       : std_logic;
   signal ib2_up_eof_n       : std_logic;
   signal ib2_up_src_rdy_n   : std_logic;
   signal ib2_up_dst_rdy_n   : std_logic;
   
   -- Internal Bus u64 (Switch0 <-> USER IB64)
   signal ib_u64_down_data      : std_logic_vector(63 downto 0);
   signal ib_u64_down_sof_n     : std_logic;
   signal ib_u64_down_eof_n     : std_logic;
   signal ib_u64_down_src_rdy_n : std_logic;
   signal ib_u64_down_dst_rdy_n : std_logic;
   signal ib_u64_up_data        : std_logic_vector(63 downto 0);
   signal ib_u64_up_sof_n       : std_logic;
   signal ib_u64_up_eof_n       : std_logic;
   signal ib_u64_up_src_rdy_n   : std_logic;
   signal ib_u64_up_dst_rdy_n   : std_logic;
   
   -- Memory Interface 0 (Endpoint0 <-> MI_Splitter_plus0)
   signal mi0_dwr       : std_logic_vector(31 downto 0);
   signal mi0_addr      : std_logic_vector(31 downto 0);
   signal mi0_rd        : std_logic;
   signal mi0_wr        : std_logic;
   signal mi0_ardy      : std_logic;
   signal mi0_be        : std_logic_vector(3 downto 0);
   signal mi0_drd       : std_logic_vector(31 downto 0);
   signal mi0_drdy      : std_logic;
   
   -- Memory Interface 1 (MI_Splitter_plus0 <-> MI_Splitter1)
   signal mi1_dwr       : std_logic_vector(31 downto 0);
   signal mi1_addr      : std_logic_vector(31 downto 0);
   signal mi1_rd        : std_logic;
   signal mi1_wr        : std_logic;
   signal mi1_ardy      : std_logic;
   signal mi1_be        : std_logic_vector(3 downto 0);
   signal mi1_drd       : std_logic_vector(31 downto 0);
   signal mi1_drdy      : std_logic;
   
   -- Memory Interface 2 (MI_Splitter1 <-> MI_Splitter2)
   signal mi2_dwr       : std_logic_vector(31 downto 0);
   signal mi2_addr      : std_logic_vector(15 downto 0);
   signal mi2_rd        : std_logic;
   signal mi2_wr        : std_logic;
   signal mi2_ardy      : std_logic;
   signal mi2_be        : std_logic_vector(3 downto 0);
   signal mi2_drd       : std_logic_vector(31 downto 0);
   signal mi2_drdy      : std_logic;
   
   -- Memory Interface 3 (MI_Splitter2 <-> MI_Splitter3)
   signal mi3_dwr       : std_logic_vector(31 downto 0);
   signal mi3_addr      : std_logic_vector(13 downto 0);
   signal mi3_rd        : std_logic;
   signal mi3_wr        : std_logic;
   signal mi3_ardy      : std_logic;
   signal mi3_be        : std_logic_vector(3 downto 0);
   signal mi3_drd       : std_logic_vector(31 downto 0);
   signal mi3_drdy      : std_logic;
   
   -- Memory Interface 4 (MI_Splitter2 <-> MI_Pipe to TSU)
   signal mi4_dwr       : std_logic_vector(31 downto 0);
   signal mi4_addr      : std_logic_vector(13 downto 0);
   signal mi4_rd        : std_logic;
   signal mi4_wr        : std_logic;
   signal mi4_ardy      : std_logic;
   signal mi4_be        : std_logic_vector(3 downto 0);
   signal mi4_drd       : std_logic_vector(31 downto 0);
   signal mi4_drdy      : std_logic;
   
   -- Memory Interface 5 (MI_Splitter2 <-> MI_Pipe to DMA)
   signal mi5_dwr       : std_logic_vector(31 downto 0);
   signal mi5_addr      : std_logic_vector(13 downto 0);
   signal mi5_rd        : std_logic;
   signal mi5_wr        : std_logic;
   signal mi5_ardy      : std_logic;
   signal mi5_be        : std_logic_vector(3 downto 0);
   signal mi5_drd       : std_logic_vector(31 downto 0);
   signal mi5_drdy      : std_logic;
   
   -- Memory Interface 6 (MI_Splitter2 <-> MI_Pipe to NET)
   signal mi6_dwr       : std_logic_vector(31 downto 0);
   signal mi6_addr      : std_logic_vector(13 downto 0);
   signal mi6_rd        : std_logic;
   signal mi6_wr        : std_logic;
   signal mi6_ardy      : std_logic;
   signal mi6_be        : std_logic_vector(3 downto 0);
   signal mi6_drd       : std_logic_vector(31 downto 0);
   signal mi6_drdy      : std_logic;
   
   -- auxiliary signals needed due to connection to chipscope
   signal DMA_RD_aux    : std_logic;
   signal DMA_WR_aux    : std_logic;
   signal NET_RD_aux    : std_logic;
   signal NET_WR_aux    : std_logic;
   signal USER_MI32_RD_aux  : std_logic;
   signal USER_MI32_WR_aux  : std_logic;
   
   -- Chipscope signals
   signal control0            : std_logic_vector(35 downto 0);
   signal control1            : std_logic_vector(35 downto 0);
   signal control2            : std_logic_vector(35 downto 0);
   signal ila144_1_trig       : std_logic_vector(143 downto 0);
   signal ila72_2_trig        : std_logic_vector(71 downto 0);
   signal ila144_3_trig       : std_logic_vector(143 downto 0);
   
   signal cntr_down           : std_logic_vector(8 downto 0);
   signal cntr_up             : std_logic_vector(8 downto 0);
   
--    -- Attributes (Precision)
--    attribute dont_touch : string;
--    attribute dont_touch of ICON3_I       : label is "true";
--    attribute dont_touch of ILA144_1_I    : label is "true";
--    attribute dont_touch of ILA72_2_I     : label is "true";
--    attribute dont_touch of ILA144_3_I    : label is "true";
   
begin
   
   
   -- -------------------------------------------------------------------------
   --                         INTERCONNECTION SYSTEM 
   -- -------------------------------------------------------------------------
   
   -- ICS to GICS converter ---------------------------------------------------
   -- This is needed because PCI Express bridge uses old ICS packet format
   IB_ICS2GICS_I: entity work.ICS2GICS
   generic map(
      DATA_WIDTH     => 64
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK            => CLK,
      RESET          => RESET,
      
      -- ICS interface --------------------------------------------------------
      ICS_IN_DATA         => PCI_IB_DOWN_DATA,
      ICS_IN_SOF_N        => PCI_IB_DOWN_SOP_N,
      ICS_IN_EOF_N        => PCI_IB_DOWN_EOP_N,
      ICS_IN_SRC_RDY_N    => PCI_IB_DOWN_SRC_RDY_N,
      ICS_IN_DST_RDY_N    => PCI_IB_DOWN_DST_RDY_N,
      
      ICS_OUT_DATA        => PCI_IB_UP_DATA,
      ICS_OUT_SOF_N       => PCI_IB_UP_SOP_N,
      ICS_OUT_EOF_N       => PCI_IB_UP_EOP_N,
      ICS_OUT_SRC_RDY_N   => PCI_IB_UP_SRC_RDY_N,
      ICS_OUT_DST_RDY_N   => PCI_IB_UP_DST_RDY_N,
      
      -- GICS interface -------------------------------------------------------
      GICS_IN_DATA        => ib0_up_data,
      GICS_IN_SOF_N       => ib0_up_sof_n,
      GICS_IN_EOF_N       => ib0_up_eof_n,
      GICS_IN_SRC_RDY_N   => ib0_up_src_rdy_n,
      GICS_IN_DST_RDY_N   => ib0_up_dst_rdy_n,
      
      GICS_OUT_DATA       => ib0_down_data,
      GICS_OUT_SOF_N      => ib0_down_sof_n,
      GICS_OUT_EOF_N      => ib0_down_eof_n,
      GICS_OUT_SRC_RDY_N  => ib0_down_src_rdy_n,
      GICS_OUT_DST_RDY_N  => ib0_down_dst_rdy_n
   );
   
   -- Switch 0 ----------------------------------------------------------------
   IB_SWITCH0_I: entity work.IB_SWITCH_MASTER
   generic map(
      -- Data Width
      DATA_WIDTH     => 64,
      -- The number of headers to be stored
      HEADER_NUM     => IBS0_HEADER_NUM,
      -- Port 1 Address Space
      PORT1_BASE     => IBS0_PORT1_BASE,
      PORT1_LIMIT    => IBS0_PORT1_LIMIT,
      -- Port 2 Address Space
      PORT2_BASE     => IBS0_PORT2_BASE,
      PORT2_LIMIT    => IBS0_PORT2_LIMIT
   )
   port map(
      -- Common Interface
      CLK        => CLK,
      RESET      => RESET,
      -- Upstream Port
      PORT0_DOWN_DATA       => ib0_down_data,
      PORT0_DOWN_SOF_N      => ib0_down_sof_n,
      PORT0_DOWN_EOF_N      => ib0_down_eof_n,
      PORT0_DOWN_SRC_RDY_N  => ib0_down_src_rdy_n,
      PORT0_DOWN_DST_RDY_N  => ib0_down_dst_rdy_n,
      PORT0_UP_DATA         => ib0_up_data,
      PORT0_UP_SOF_N        => ib0_up_sof_n,
      PORT0_UP_EOF_N        => ib0_up_eof_n,
      PORT0_UP_SRC_RDY_N    => ib0_up_src_rdy_n,
      PORT0_UP_DST_RDY_N    => ib0_up_dst_rdy_n,
      -- Downstream Ports
      PORT1_DOWN_DATA       => ib1_down_data,
      PORT1_DOWN_SOF_N      => ib1_down_sof_n,
      PORT1_DOWN_EOF_N      => ib1_down_eof_n,
      PORT1_DOWN_SRC_RDY_N  => ib1_down_src_rdy_n,
      PORT1_DOWN_DST_RDY_N  => ib1_down_dst_rdy_n,
      PORT1_UP_DATA         => ib1_up_data,
      PORT1_UP_SOF_N        => ib1_up_sof_n,
      PORT1_UP_EOF_N        => ib1_up_eof_n,
      PORT1_UP_SRC_RDY_N    => ib1_up_src_rdy_n,
      PORT1_UP_DST_RDY_N    => ib1_up_dst_rdy_n,
      
      PORT2_DOWN_DATA       => ib_u64_down_data,
      PORT2_DOWN_SOF_N      => ib_u64_down_sof_n,
      PORT2_DOWN_EOF_N      => ib_u64_down_eof_n,
      PORT2_DOWN_SRC_RDY_N  => ib_u64_down_src_rdy_n,
      PORT2_DOWN_DST_RDY_N  => ib_u64_down_dst_rdy_n,
      PORT2_UP_DATA         => ib_u64_up_data,
      PORT2_UP_SOF_N        => ib_u64_up_sof_n,
      PORT2_UP_EOF_N        => ib_u64_up_eof_n,
      PORT2_UP_SRC_RDY_N    => ib_u64_up_src_rdy_n,
      PORT2_UP_DST_RDY_N    => ib_u64_up_dst_rdy_n
   );
   
   USER_IB64_DOWN_DATA      <= ib_u64_down_data;
   USER_IB64_DOWN_SOF_N     <= ib_u64_down_sof_n;
   USER_IB64_DOWN_EOF_N     <= ib_u64_down_eof_n;
   USER_IB64_DOWN_SRC_RDY_N <= ib_u64_down_src_rdy_n;
   ib_u64_down_dst_rdy_n    <= USER_IB64_DOWN_DST_RDY_N; 
   ib_u64_up_data           <= USER_IB64_UP_DATA;
   ib_u64_up_sof_n          <= USER_IB64_UP_SOF_N;
   ib_u64_up_eof_n          <= USER_IB64_UP_EOF_N;
   ib_u64_up_src_rdy_n      <= USER_IB64_UP_SRC_RDY_N;
   USER_IB64_UP_DST_RDY_N   <= ib_u64_up_dst_rdy_n;


   -- Transformer 0 (64 to 32) ------------------------------------------------
   IB_TRANSFORMER0_I: entity work.IB_TRANSFORMER
   generic map(
      -- Data Widths
      UP_DATA_WIDTH           => 64,
      DOWN_DATA_WIDTH         => 32,
      -- Input buffers
      UP_INPUT_BUFFER_ITEMS   => IBT0_UP_INPUT_BUFFER_ITEMS,
      DOWN_INPUT_BUFFER_ITEMS => IBT0_DOWN_INPUT_BUFFER_ITEMS,
      -- Output pipes
      UP_OUTPUT_PIPE          => IBT0_UP_OUTPUT_PIPE,
      DOWN_OUTPUT_PIPE        => IBT0_DOWN_OUTPUT_PIPE
   )
   port map(
      -- Common Interface
      CLK        => CLK,
      RESET      => RESET,
      -- Up Interface
      UP_IN_DATA        => ib1_down_data,
      UP_IN_SOF_N       => ib1_down_sof_n,
      UP_IN_EOF_N       => ib1_down_eof_n,
      UP_IN_SRC_RDY_N   => ib1_down_src_rdy_n,
      UP_IN_DST_RDY_N   => ib1_down_dst_rdy_n,
      UP_OUT_DATA       => ib1_up_data,
      UP_OUT_SOF_N      => ib1_up_sof_n,
      UP_OUT_EOF_N      => ib1_up_eof_n,
      UP_OUT_SRC_RDY_N  => ib1_up_src_rdy_n,
      UP_OUT_DST_RDY_N  => ib1_up_dst_rdy_n,
      -- Down Interface
      DOWN_OUT_DATA      => ib2_down_data,
      DOWN_OUT_SOF_N     => ib2_down_sof_n,
      DOWN_OUT_EOF_N     => ib2_down_eof_n,
      DOWN_OUT_SRC_RDY_N => ib2_down_src_rdy_n,
      DOWN_OUT_DST_RDY_N => ib2_down_dst_rdy_n,
      DOWN_IN_DATA       => ib2_up_data,
      DOWN_IN_SOF_N      => ib2_up_sof_n,
      DOWN_IN_EOF_N      => ib2_up_eof_n,
      DOWN_IN_SRC_RDY_N  => ib2_up_src_rdy_n,
      DOWN_IN_DST_RDY_N  => ib2_up_dst_rdy_n
   ); 
   
   -- Endpoint 0 --------------------------------------------------------------
   IB_ENDPOINT0_I: entity work.IB_ENDPOINT_MI
   generic map(
      -- Data Width
      DATA_WIDTH         => 32,
      -- Address Width
      ADDR_WIDTH         => 32,
      -- Bus Master Enable
      BUS_MASTER_ENABLE  => false,
      -- Endpoint Address Space 
      --ENDPOINT_BASE      => IBE0_ENDPOINT_BASE,
      --ENDPOINT_LIMIT     => IBE0_ENDPOINT_LIMIT,
      -- Endpoint is connected to
      CONNECTED_TO       => SWITCH_MASTER,
      -- Data alignment (to dst. address)
      DATA_REORDER       => IBE0_DATA_REORDER,
      -- The number of reads in-process
      READ_IN_PROCESS    => 1,
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  => IBE0_INPUT_BUFFER_SIZE,
      OUTPUT_BUFFER_SIZE => IBE0_OUTPUT_BUFFER_SIZE
   )
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- IB Interface
      IB_DOWN_DATA       => ib2_down_data,
      IB_DOWN_SOF_N      => ib2_down_sof_n,
      IB_DOWN_EOF_N      => ib2_down_eof_n,
      IB_DOWN_SRC_RDY_N  => ib2_down_src_rdy_n,
      IB_DOWN_DST_RDY_N  => ib2_down_dst_rdy_n,
      IB_UP_DATA         => ib2_up_data,
      IB_UP_SOF_N        => ib2_up_sof_n,
      IB_UP_EOF_N        => ib2_up_eof_n,
      IB_UP_SRC_RDY_N    => ib2_up_src_rdy_n,
      IB_UP_DST_RDY_N    => ib2_up_dst_rdy_n,
      
      -- MI Interface
      MI_DWR    => mi0_dwr,
      MI_ADDR   => mi0_addr,
      MI_RD     => mi0_rd,
      MI_WR     => mi0_wr,
      MI_ARDY   => mi0_ardy,
      MI_BE     => mi0_be,
      MI_DRD    => mi0_drd,
      MI_DRDY   => mi0_drdy,
      
      -- Bus Master Interface
      BM_DATA           => X"00000000",
      BM_SOF_N          => '1',
      BM_EOF_N          => '1',
      BM_SRC_RDY_N      => '1',
      BM_DST_RDY_N      => open,
      BM_TAG            => open,
      BM_TAG_VLD        => open
   );
   
   -- MI Splitter plus 0 ------------------------------------------------------
   -- forking USER MI
   MI_SPLITTER0_I: entity work.MI_SPLITTER_PLUS
   generic map(
      DATA_WIDTH    => 32,
      ITEMS         => 2,
      ADDR_CMP_MASK => X"01F80000",
      PORT1_BASE    => X"00080000",
      PIPE          => SPLIT0_PIPE,
      PIPE_OUTREG   => SPLIT0_PIPE_OUTREG
   )
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Input Interface
      IN_DWR    => mi0_dwr,
      IN_ADDR   => mi0_addr,
      IN_RD     => mi0_rd,
      IN_WR     => mi0_wr,
      IN_ARDY   => mi0_ardy,
      IN_BE     => mi0_be,
      IN_DRD    => mi0_drd,
      IN_DRDY   => mi0_drdy,
      
      -- Output Interface
      OUT_DWR( 31 downto  0)  => mi1_dwr,
      OUT_DWR( 63 downto 32)  => USER_MI32_DWR,
      OUT_ADDR( 31 downto  0) => mi1_addr,
      OUT_ADDR( 63 downto 32) => USER_MI32_ADDR,
      OUT_RD(0)   => mi1_rd,
      OUT_RD(1)   => USER_MI32_RD_aux,
      OUT_WR(0)   => mi1_wr,
      OUT_WR(1)   => USER_MI32_WR_aux,
      OUT_ARDY(0) => mi1_ardy,
      OUT_ARDY(1) => USER_MI32_ARDY,
      OUT_BE( 3 downto  0)   => mi1_be,
      OUT_BE( 7 downto  4)   => USER_MI32_BE,
      OUT_DRD( 31 downto  0) => mi1_drd,
      OUT_DRD( 63 downto 32) => USER_MI32_DRD,
      OUT_DRDY(0) => mi1_drdy,
      OUT_DRDY(1) => USER_MI32_DRDY
   );
   
   USER_MI32_RD   <= USER_MI32_RD_aux;
   USER_MI32_WR   <= USER_MI32_WR_aux;
   
   -- MI Splitter 1 -----------------------------------------------------------
   -- forking MI to IFC and LSC
   MI_SPLITTER1_I: entity work.MI_SPLITTER
   generic map(
      ITEMS       => 7,
      ADDR_WIDTH  => 16,
      DATA_WIDTH  => 32,
      PIPE        => SPLIT1_PIPE,
      PIPE_OUTREG => SPLIT1_PIPE_OUTREG
   )
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Input Interface
      IN_DWR    => mi1_dwr,
      IN_ADDR   => mi1_addr(18 downto 0),
      IN_RD     => mi1_rd,
      IN_WR     => mi1_wr,
      IN_ARDY   => mi1_ardy,
      IN_BE     => mi1_be,
      IN_DRD    => mi1_drd,
      IN_DRDY   => mi1_drdy,
      
      -- Output Interface
      OUT_DWR( 31 downto   0)  => mi2_dwr,
      OUT_DWR( 63 downto  32)  => IFC1_DWR,
      OUT_DWR( 95 downto  64)  => IFC2_DWR,
      OUT_DWR(127 downto  96)  => LSC1_DWR,
      OUT_DWR(159 downto 128)  => LSC2_DWR,
      OUT_DWR(191 downto 160)  => LSC3_DWR,
      OUT_DWR(223 downto 192)  => LSC4_DWR,
      OUT_ADDR( 15 downto   0) => mi2_addr(15 downto 0),
      OUT_ADDR( 31 downto  16) => IFC1_ADDR(15 downto 0),
      OUT_ADDR( 47 downto  32) => IFC2_ADDR(15 downto 0),
      OUT_ADDR( 63 downto  48) => LSC1_ADDR(15 downto 0),
      OUT_ADDR( 79 downto  64) => LSC2_ADDR(15 downto 0),
      OUT_ADDR( 95 downto  80) => LSC3_ADDR(15 downto 0),
      OUT_ADDR(111 downto  96) => LSC4_ADDR(15 downto 0),
      OUT_RD(0)  => mi2_rd,
      OUT_RD(1)  => IFC1_RD,
      OUT_RD(2)  => IFC2_RD,
      OUT_RD(3)  => LSC1_RD,
      OUT_RD(4)  => LSC2_RD,
      OUT_RD(5)  => LSC3_RD,
      OUT_RD(6)  => LSC4_RD,
      OUT_WR(0)  => mi2_wr,
      OUT_WR(1)  => IFC1_WR,
      OUT_WR(2)  => IFC2_WR,
      OUT_WR(3)  => LSC1_WR,
      OUT_WR(4)  => LSC2_WR,
      OUT_WR(5)  => LSC3_WR,
      OUT_WR(6)  => LSC4_WR,
      OUT_ARDY(0)  => mi2_ardy,
      OUT_ARDY(1)  => IFC1_ARDY,
      OUT_ARDY(2)  => IFC2_ARDY,
      OUT_ARDY(3)  => LSC1_ARDY,
      OUT_ARDY(4)  => LSC2_ARDY,
      OUT_ARDY(5)  => LSC3_ARDY,
      OUT_ARDY(6)  => LSC4_ARDY,
      OUT_BE( 3 downto  0)  => mi2_be,
      OUT_BE( 7 downto  4)  => IFC1_BE,
      OUT_BE(11 downto  8)  => IFC2_BE,
      OUT_BE(15 downto 12)  => LSC1_BE,
      OUT_BE(19 downto 16)  => LSC2_BE,
      OUT_BE(23 downto 20)  => LSC3_BE,
      OUT_BE(27 downto 24)  => LSC4_BE,
      OUT_DRD( 31 downto   0)  => mi2_drd,
      OUT_DRD( 63 downto  32)  => IFC1_DRD,
      OUT_DRD( 95 downto  64)  => IFC2_DRD,
      OUT_DRD(127 downto  96)  => LSC1_DRD,
      OUT_DRD(159 downto 128)  => LSC2_DRD,
      OUT_DRD(191 downto 160)  => LSC3_DRD,
      OUT_DRD(223 downto 192)  => LSC4_DRD,
      OUT_DRDY(0)  => mi2_drdy,
      OUT_DRDY(1)  => IFC1_DRDY,
      OUT_DRDY(2)  => IFC2_DRDY,
      OUT_DRDY(3)  => LSC1_DRDY,
      OUT_DRDY(4)  => LSC2_DRDY,
      OUT_DRDY(5)  => LSC3_DRDY,
      OUT_DRDY(6)  => LSC4_DRDY
   );
   
   -- MI Splitter 2 -----------------------------------------------------------
   MI_SPLITTER2_I: entity work.MI_SPLITTER
   generic map(
      ITEMS       => 4,
      ADDR_WIDTH  => 14,
      DATA_WIDTH  => 32,
      PIPE        => SPLIT2_PIPE,
      PIPE_OUTREG => SPLIT2_PIPE_OUTREG
   )
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Input Interface
      IN_DWR    => mi2_dwr,
      IN_ADDR   => mi2_addr,
      IN_RD     => mi2_rd,
      IN_WR     => mi2_wr,
      IN_ARDY   => mi2_ardy,
      IN_BE     => mi2_be,
      IN_DRD    => mi2_drd,
      IN_DRDY   => mi2_drdy,
      
      -- Output Interface
      OUT_DWR( 31 downto  0) => mi3_dwr,
      OUT_DWR( 63 downto 32) => mi6_dwr,
      OUT_DWR( 95 downto 64) => mi4_dwr,
      OUT_DWR(127 downto 96) => mi5_dwr,
      OUT_ADDR(13 downto  0) => mi3_addr,
      OUT_ADDR(27 downto 14) => mi6_addr,
      OUT_ADDR(41 downto 28) => mi4_addr,
      OUT_ADDR(55 downto 42) => mi5_addr,
      OUT_RD(0)   => mi3_rd,
      OUT_RD(1)   => mi6_rd,
      OUT_RD(2)   => mi4_rd,
      OUT_RD(3)   => mi5_rd,
      OUT_WR(0)   => mi3_wr,
      OUT_WR(1)   => mi6_wr,
      OUT_WR(2)   => mi4_wr,
      OUT_WR(3)   => mi5_wr,
      OUT_ARDY(0) => mi3_ardy,
      OUT_ARDY(1) => mi6_ardy,
      OUT_ARDY(2) => mi4_ardy,
      OUT_ARDY(3) => mi5_ardy,
      OUT_BE( 3 downto  0)   => mi3_be,
      OUT_BE( 7 downto  4)   => mi6_be,
      OUT_BE(11 downto  8)   => mi4_be,
      OUT_BE(15 downto 12)   => mi5_be,
      OUT_DRD( 31 downto  0) => mi3_drd,
      OUT_DRD( 63 downto 32) => mi6_drd,
      OUT_DRD( 95 downto 64) => mi4_drd,
      OUT_DRD(127 downto 96) => mi5_drd,
      OUT_DRDY(0) => mi3_drdy,
      OUT_DRDY(1) => mi6_drdy,
      OUT_DRDY(2) => mi4_drdy,
      OUT_DRDY(3) => mi5_drdy
   );
   
   -- MI Splitter 3 -----------------------------------------------------------
   MI_SPLITTER3_I: entity work.MI_SPLITTER
   generic map(
      ITEMS       => 2,
      ADDR_WIDTH  => 10,
      DATA_WIDTH  => 32,
      PIPE        => SPLIT3_PIPE,
      PIPE_OUTREG => SPLIT3_PIPE_OUTREG
   )
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      
      -- Input Interface
      IN_DWR    => mi3_dwr,
      IN_ADDR   => mi3_addr(10 downto 0),
      IN_RD     => mi3_rd,
      IN_WR     => mi3_wr,
      IN_ARDY   => mi3_ardy,
      IN_BE     => mi3_be,
      IN_DRD    => mi3_drd,
      IN_DRDY   => mi3_drdy,
      
      -- Output Interface
      OUT_DWR(31 downto  0)  => ID_DWR,
      OUT_DWR(63 downto 32)  => PHY_DWR,
      OUT_ADDR( 9 downto  0) => ID_ADDR(9 downto 0),
      OUT_ADDR(19 downto 10) => PHY_ADDR(9 downto 0),
      OUT_RD(0)   => ID_RD,
      OUT_RD(1)   => PHY_RD,
      OUT_WR(0)   => ID_WR,
      OUT_WR(1)   => PHY_WR,
      OUT_ARDY(0) => ID_ARDY,
      OUT_ARDY(1) => PHY_ARDY,
      OUT_BE( 3 downto  0)  => ID_BE,
      OUT_BE( 7 downto  4)  => PHY_BE,
      OUT_DRD(31 downto  0) => ID_DRD,
      OUT_DRD(63 downto 32) => PHY_DRD,
      OUT_DRDY(0) => ID_DRDY,
      OUT_DRDY(1) => PHY_DRDY
   );
   
   ID_ADDR (31 downto 10) <= (others => '0');
   PHY_ADDR(31 downto 10) <= (others => '0');
   
   -- MI Pipe to TSU ----------------------------------------------------------
   MI_PIPE1_I: entity work.MI_PIPE
   generic map(
      ADDR_WIDTH => 14,
      DATA_WIDTH => 32,
      USE_OUTREG => PIPE_TSU_OUTREG,
      FAKE_PIPE  => not PIPE_TSU
   )
   port map(
      -- Common Interface
      CLK       => CLK,
      RESET     => RESET,
      
      -- Input Interface
      IN_DWR    => mi4_dwr,
      IN_ADDR   => mi4_addr,
      IN_RD     => mi4_rd,
      IN_WR     => mi4_wr,
      IN_ARDY   => mi4_ardy,
      IN_BE     => mi4_be,
      IN_DRD    => mi4_drd,
      IN_DRDY   => mi4_drdy,
      
      -- Output Interface
      OUT_DWR   => TSU_DWR,
      OUT_ADDR  => TSU_ADDR(13 downto 0),
      OUT_RD    => TSU_RD,
      OUT_WR    => TSU_WR,
      OUT_ARDY  => TSU_ARDY,
      OUT_BE    => TSU_BE,
      OUT_DRD   => TSU_DRD,
      OUT_DRDY  => TSU_DRDY
   );

   TSU_ADDR(31 downto 14) <= (others => '0');
   
   -- MI Pipe to DMA ----------------------------------------------------------
   MI_PIPE2_I: entity work.MI_PIPE
   generic map(
      ADDR_WIDTH => 14,
      DATA_WIDTH => 32,
      USE_OUTREG => PIPE_DMA_OUTREG,
      FAKE_PIPE  => not PIPE_DMA
   )
   port map(
      -- Common Interface
      CLK       => CLK,
      RESET     => RESET,
      
      -- Input Interface
      IN_DWR    => mi5_dwr,
      IN_ADDR   => mi5_addr,
      IN_RD     => mi5_rd,
      IN_WR     => mi5_wr,
      IN_ARDY   => mi5_ardy,
      IN_BE     => mi5_be,
      IN_DRD    => mi5_drd,
      IN_DRDY   => mi5_drdy,
      
      -- Output Interface
      OUT_DWR   => DMA_DWR,
      OUT_ADDR  => DMA_ADDR(13 downto 0),
      OUT_RD    => DMA_RD_aux,
      OUT_WR    => DMA_WR_aux,
      OUT_ARDY  => DMA_ARDY,
      OUT_BE    => DMA_BE,
      OUT_DRD   => DMA_DRD,
      OUT_DRDY  => DMA_DRDY
   );
   
   DMA_ADDR(31 downto 14) <= (others => '0');
   
   DMA_RD <= DMA_RD_aux;
   DMA_WR <= DMA_WR_aux;
   
   -- MI Pipe to NET ----------------------------------------------------------
   MI_PIPE3_I: entity work.MI_PIPE
   generic map(
      ADDR_WIDTH => 14,
      DATA_WIDTH => 32,
      USE_OUTREG => PIPE_NET_OUTREG,
      FAKE_PIPE  => not PIPE_NET
   )
   port map(
      -- Common Interface
      CLK       => CLK,
      RESET     => RESET,
      
      -- Input Interface
      IN_DWR    => mi6_dwr,
      IN_ADDR   => mi6_addr,
      IN_RD     => mi6_rd,
      IN_WR     => mi6_wr,
      IN_ARDY   => mi6_ardy,
      IN_BE     => mi6_be,
      IN_DRD    => mi6_drd,
      IN_DRDY   => mi6_drdy,
      
      -- Output Interface
      OUT_DWR   => NET_DWR,
      OUT_ADDR  => NET_ADDR(13 downto 0),
      OUT_RD    => NET_RD_aux,
      OUT_WR    => NET_WR_aux,
      OUT_ARDY  => NET_ARDY,
      OUT_BE    => NET_BE,
      OUT_DRD   => NET_DRD,
      OUT_DRDY  => NET_DRDY
   );
   
   NET_ADDR(31 downto 14) <= (others => '0');
   
   NET_RD <= NET_RD_aux;
   NET_WR <= NET_WR_aux;
   
   -- -------------------------------------------------------------------------
   --                             CHIPSCOPE
   -- -------------------------------------------------------------------------
   
--    cntrs: process(CLK)
--    begin
--       if (CLK'event and CLK='1') then
--          if (ib0_up_dst_rdy_n = '0') then
--             cntr_up <= (others => '0');
--          else
--             cntr_up <= cntr_up + 1;
--          end if;
--          if (ib0_down_dst_rdy_n = '0') then
--             cntr_down <= (others => '0');
--          else
--             cntr_down <= cntr_down + 1;
--          end if;
--       end if;
--    end process;
--    
--    -- Chipscope ICON with 3 ports
--    ICON3_I : icon3
--    port map(
--      CONTROL0 => control0,
--      CONTROL1 => control1,
--      CONTROL2 => control2
--    );
-- 
--    -- Top 64bit Internal Bus
--    ila144_1_trig <= --"00000000"          -- unused (8 bits)
--                     cntr_down(8 downto 5)
--                   & cntr_up(8 downto 5)
--                   & ib0_down_data       -- downstrem port
--                   & ib0_down_sof_n
--                   & ib0_down_eof_n
--                   & ib0_down_src_rdy_n
--                   & ib0_down_dst_rdy_n
--                   & ib0_up_data         -- upstrem port
--                   & ib0_up_sof_n
--                   & ib0_up_eof_n
--                   & ib0_up_src_rdy_n
--                   & ib0_up_dst_rdy_n;
-- 
--    ILA144_1_I : ila144
--    port map(
--       CONTROL => control0,
--       CLK     => CLK,
--       TRIG0   => ila144_1_trig
--    );
--    
--    -- 32bit Internal Bus to Endpoint
--    ila72_2_trig  <= ib2_down_data
--                   & ib2_down_sof_n
--                   & ib2_down_eof_n
--                   & ib2_down_src_rdy_n
--                   & ib2_down_dst_rdy_n
--                   & ib2_up_data
--                   & ib2_up_sof_n
--                   & ib2_up_eof_n
--                   & ib2_up_src_rdy_n
--                   & ib2_up_dst_rdy_n;
-- 
--    ILA72_2_I : ila72
--    port map(
--       CONTROL => control1,
--       CLK     => CLK,
--       TRIG0   => ila72_2_trig
--    );
--    
--    -- MI bus
--    ila144_3_trig <= --X"000000" & "00" -- 26 usnused bits
--                     X"0000" & "00" -- 18 unused
--                   & cntr_down(8 downto 5)
--                   & cntr_up(8 downto 5)
--                   & PHY_DRDY
--                   & TSU_DRDY
-- 
--                   & DMA_RD_aux       -- MI to DMA module (only control signals)
--                   & DMA_WR_aux
--                   & DMA_ARDY
--                   & DMA_DRDY
--                     
--                   & NET_RD_aux       -- MI to Network module (only control signals)
--                   & NET_WR_aux
--                   & NET_ARDY
--                   & NET_DRDY
--                     
--                   & USER_MI32_RD_aux   -- MI to Application (only control signals)
--                   & USER_MI32_WR_aux
--                   & USER_MI32_ARDY
--                   & USER_MI32_DRDY
--                        
--                   & mi0_dwr      -- Main MI
--                   & mi0_addr
--                   & mi0_rd
--                   & mi0_wr
--                   & mi0_ardy
--                   & mi0_be
--                   & mi0_drd
--                   & mi0_drdy;
--                  
--                  
--    ILA144_3_I : ila144
--    port map(
--       CONTROL => control2,
--       CLK     => CLK,
--       TRIG0   => ila144_3_trig
--    );
   
end architecture structural;
