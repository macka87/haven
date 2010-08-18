-- application.vhd : Combov2 NetCOPE application module
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all; 
use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.addr_space.all;
use work.network_mod_10g2_64_const.all;
Library UNISIM;
use UNISIM.vcomponents.all;

architecture full of APPLICATION is

   constant WATCHER : boolean := true;

   component tsu_async is
   -- PORTS
   port (
      RESET          : in std_logic;

      -- Input interface
      IN_CLK         : in std_logic;

      IN_TS          : in std_logic_vector(63 downto 0);
      IN_TS_DV       : in std_logic;

      -- Output interface
      OUT_CLK        : in std_logic;

      OUT_TS         : out std_logic_vector(63 downto 0);
      OUT_TS_DV      : out std_logic
   );
   end component tsu_async;

component IB_ENDPOINT_SYNTH 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH         : integer := 64;
      -- Address Width (1-32)
      ADDR_WIDTH         : integer := 32
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK               : in std_logic;  
      RESET             : in std_logic;  

      -- IB Interface ---------------------------------------------------------
      IB_DOWN_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;

      IB_UP_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;      

      -- Write Interface ------------------------------------------------------
      WR_REQ            : out std_logic;                           
      WR_RDY            : in  std_logic;                                 
      WR_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);       
      WR_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);        
      WR_LENGTH         : out std_logic_vector(11 downto 0);       
      WR_SOF            : out std_logic;                           
      WR_EOF            : out std_logic;

      -- Read Interface -------------------------------------------------------
      RD_REQ            : out std_logic;                           
      RD_ARDY_ACCEPT    : in  std_logic;                           
      RD_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);        
      RD_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);       
      RD_LENGTH         : out std_logic_vector(11 downto 0);       
      RD_SOF            : out std_logic;                           
      RD_EOF            : out std_logic;                    

      RD_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0); 
      RD_SRC_RDY        : in  std_logic;                           
      RD_DST_RDY        : out std_logic;

      -- Bus Master Interface -------------------------------------------------
      BM_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      BM_SOF_N          : in  std_logic;
      BM_EOF_N          : in  std_logic;
      BM_SRC_RDY_N      : in  std_logic;
      BM_DST_RDY_N      : out std_logic;

      BM_TAG            : out std_logic_vector(7 downto 0);
      BM_TAG_VLD        : out std_logic
  );
end component;

component FL_WATCH_2 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(1 downto 0);
      EOF_N          : in std_logic_vector(1 downto 0);
      SOP_N          : in std_logic_vector(1 downto 0);
      EOP_N          : in std_logic_vector(1 downto 0);
      DST_RDY_N      : in std_logic_vector(1 downto 0);
      SRC_RDY_N      : in std_logic_vector(1 downto 0);

      FRAME_ERR      : out std_logic_vector(1 downto 0);

      MI_DWR	      : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	         : in std_logic;
      MI_WR	         : in std_logic;
      MI_BE	         : in std_logic_vector(3 downto 0);
      MI_DRD         : out std_logic_vector(31 downto 0);
      MI_ARDY        : out std_logic;
      MI_DRDY        : out std_logic
   );
end component;
-- ----------------------------------------------------------------------------
--                            Signal declaration
-- ----------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                             MI signals
   -- -------------------------------------------------------------------------
   -- MI32 to experimental BRAM and registers
   signal mi32_exp_dwr           : std_logic_vector(31 downto 0);
   signal mi32_exp_addr          : std_logic_vector(31 downto 0);
   signal reg_mi32_exp_addr_9    : std_logic;
   signal mi32_exp_rd            : std_logic;
   signal mi32_exp_wr            : std_logic;
   signal mi32_exp_be            : std_logic_vector(3 downto 0);
   signal mi32_exp_drd           : std_logic_vector(31 downto 0);
   signal mi32_exp_ardy          : std_logic;
   signal mi32_exp_drdy          : std_logic;

   -- MI32 to MI_SPLITTER for FL_WATCH instances
   signal mi32_watch_dwr         : std_logic_vector(31 downto 0);
   signal mi32_watch_addr        : std_logic_vector(31 downto 0);
   signal mi32_watch_rd          : std_logic;
   signal mi32_watch_wr          : std_logic;
   signal mi32_watch_be          : std_logic_vector(3 downto 0);
   signal mi32_watch_drd         : std_logic_vector(31 downto 0);
   signal mi32_watch_ardy        : std_logic;
   signal mi32_watch_drdy        : std_logic;

   -- MI32 to FL_WATCH in TX direction (application -> obuf)
   signal mi32_tx_watch_dwr      : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_addr     : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_rd       : std_logic;
   signal mi32_tx_watch_wr       : std_logic;
   signal mi32_tx_watch_be       : std_logic_vector(3 downto 0);
   signal mi32_tx_watch_drd      : std_logic_vector(31 downto 0);
   signal mi32_tx_watch_ardy     : std_logic;
   signal mi32_tx_watch_drdy     : std_logic;

   -- MI32 to FL_WATCH in RX direction (application <- ibuf)
   signal mi32_rx_watch_dwr      : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_addr     : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_rd       : std_logic;
   signal mi32_rx_watch_wr       : std_logic;
   signal mi32_rx_watch_be       : std_logic_vector(3 downto 0);
   signal mi32_rx_watch_drd      : std_logic_vector(31 downto 0);
   signal mi32_rx_watch_ardy     : std_logic;
   signal mi32_rx_watch_drdy     : std_logic;

   -- -------------------------------------------------------------------------
   --                        FrameLink signals
   -- -------------------------------------------------------------------------
   -- signals to FL_WATCH
   signal fl_watch_rx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_rx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_watch_rx_dst_rdy_n : std_logic_vector(1 downto 0);

   signal fl_watch_tx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_watch_tx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_watch_tx_dst_rdy_n : std_logic_vector(1 downto 0);

   -- -------------------------------------------------------------------------
   --                         Example instance signals
   -- -------------------------------------------------------------------------
   signal bram_do          : std_logic_vector(31 downto 0);

   signal we_bram          : std_logic;
   signal we_experiment0   : std_logic;
   signal we_experiment1   : std_logic;
   signal we_experiment2   : std_logic;

   signal cs_bram          : std_logic;
   signal cs_experiment0   : std_logic;
   signal cs_experiment1   : std_logic;
   signal cs_experiment2   : std_logic;

   signal reg_do           : std_logic_vector(31 downto 0);
   signal reg_experiment0  : std_logic_vector(31 downto 0);
   signal reg_experiment1  : std_logic_vector(31 downto 0);
   signal reg_experiment2  : std_logic_vector(31 downto 0);

   -- Signals Internal Bus Endpoint signals
   signal ibep_wr_req         : std_logic;
   signal ibep_rd_req         : std_logic;
   signal reg_ibep_rd_req     : std_logic;
   signal ibep_rd_dst_rdy     : std_logic;

   signal ibep_dwr            : std_logic_vector(63 downto 0);
   signal ibep_wr_be          : std_logic_vector(7 downto 0);
   signal ibep_wraddr         : std_logic_vector(31 downto 0);
   signal ibep_rdaddr         : std_logic_vector(31 downto 0);
   signal ibep_wr             : std_logic;
   signal ibep_rd             : std_logic;
   signal ibep_drd            : std_logic_vector(63 downto 0);
   signal ibep_ack            : std_logic;

   signal reg_ibep_drdy       : std_logic;
   -- -------------------------------------------------------------------------
   --                         Pacodag signals
   -- -------------------------------------------------------------------------
   signal ts_sync               : std_logic_vector(63 downto 0);
   signal ts_dv_sync            : std_logic;

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                             FrameLink
   -- -------------------------------------------------------------------------
   -- DMA -> NET
   OBUF0_RX_DATA     <= RX0_DATA;
   OBUF0_RX_REM      <= RX0_DREM;
   OBUF0_RX_SOF_N    <= RX0_SOF_N;
   OBUF0_RX_EOF_N    <= RX0_EOF_N;
   OBUF0_RX_SOP_N    <= RX0_SOP_N;
   OBUF0_RX_EOP_N    <= RX0_EOP_N;
   OBUF0_RX_SRC_RDY_N<= RX0_SRC_RDY_N;
   RX0_DST_RDY_N     <= OBUF0_RX_DST_RDY_N;

   OBUF1_RX_DATA     <= RX1_DATA;
   OBUF1_RX_REM      <= RX1_DREM;
   OBUF1_RX_SOF_N    <= RX1_SOF_N;
   OBUF1_RX_EOF_N    <= RX1_EOF_N;
   OBUF1_RX_SOP_N    <= RX1_SOP_N;
   OBUF1_RX_EOP_N    <= RX1_EOP_N;
   OBUF1_RX_SRC_RDY_N<= RX1_SRC_RDY_N;
   RX1_DST_RDY_N     <= OBUF1_RX_DST_RDY_N;

   -- NET -> DMA
   TX0_DATA          <= IBUF0_TX_DATA;
   TX0_DREM          <= IBUF0_TX_REM;
   TX0_SOF_N         <= IBUF0_TX_SOF_N;
   TX0_EOF_N         <= IBUF0_TX_EOF_N;
   TX0_SOP_N         <= IBUF0_TX_SOP_N;
   TX0_EOP_N         <= IBUF0_TX_EOP_N;
   TX0_SRC_RDY_N     <= IBUF0_TX_SRC_RDY_N;
   IBUF0_TX_DST_RDY_N<= TX0_DST_RDY_N;

   TX1_DATA          <= IBUF1_TX_DATA;
   TX1_DREM          <= IBUF1_TX_REM;
   TX1_SOF_N         <= IBUF1_TX_SOF_N;
   TX1_EOF_N         <= IBUF1_TX_EOF_N;
   TX1_SOP_N         <= IBUF1_TX_SOP_N;
   TX1_EOP_N         <= IBUF1_TX_EOP_N;
   TX1_SRC_RDY_N     <= IBUF1_TX_SRC_RDY_N;
   IBUF1_TX_DST_RDY_N<= TX1_DST_RDY_N;

GENEREATE_WATCH: if (WATCHER = true) generate
   -- -------------------------------------------------------------------------
   --                             MI32 BUS
   -- -------------------------------------------------------------------------

   -- MI_SPLITTER between FL_WATCH units (high) and Example BRAM+regs (low)
   -- Input space globally: 0x10000 to 0x1FFFF
   -- Output space 0 glob: 0x10000 to 0x10FFF, locally shown: 0x0000 to 0x0FFF
   -- Output space 1 glob: 0x11000 to 0x11FFF, locally shown: 0x1000 to 0x1FFF
   -- Higher addresses repeating.
   -- (space 0 is also from 0x12000 to 0x12FFF,
   --  space 1 is also from 0x13000 to 0x13FFF, ... )
   MI_SPLITTER_I: entity work.MI_SPLITTER
   generic map(
      ITEMS      => 2,
      ADDR_WIDTH => 12,
      DATA_WIDTH => 32,
      PIPE       => false
   )
   port map(
      -- Common interface
      CLK      => CLK,
      RESET    => RESET,

      -- Input MI interface
      IN_DWR   => MI32_DWR,
      IN_ADDR  => MI32_ADDR(12 downto 0),
      IN_BE    => MI32_BE,
      IN_RD    => MI32_RD,
      IN_WR    => MI32_WR,
      IN_ARDY  => MI32_ARDY,
      IN_DRD   => MI32_DRD,
      IN_DRDY  => MI32_DRDY,

      -- Output MI interfaces
      OUT_DWR(31 downto 0)    => mi32_exp_dwr,
      OUT_DWR(63 downto 32)   => mi32_watch_dwr,
      OUT_ADDR(11 downto 0)   => mi32_exp_addr(11 downto 0),
      OUT_ADDR(23 downto 12)  => mi32_watch_addr(11 downto 0),
      OUT_BE(3 downto 0)      => mi32_exp_be,
      OUT_BE(7 downto 4)      => mi32_watch_be,
      OUT_RD(0)               => mi32_exp_rd,
      OUT_RD(1)               => mi32_watch_rd,
      OUT_WR(0)               => mi32_exp_wr,
      OUT_WR(1)               => mi32_watch_wr,
      OUT_ARDY(0)             => mi32_exp_ardy,
      OUT_ARDY(1)             => mi32_watch_ardy,
      OUT_DRD(31 downto 0)    => mi32_exp_drd,
      OUT_DRD(63 downto 32)   => mi32_watch_drd,
      OUT_DRDY(0)             => mi32_exp_drdy,
      OUT_DRDY(1)             => mi32_watch_drdy
   );
   
   -- MI_SPLITTER for both FL_WATCH units - RX low, TX high
   -- Input space globally 0x11000 to 0x113FF, locally shown: 0x000 to 0x3FF
   -- Output space 0 globally 0x10000 to 0x1001F, locally shown: 0x00 to 0x1F
   -- Output space 1 globally 0x10020 to 0x1003F, locally shown: 0x00 to 0x1F
   -- Higher addresses repeating.
   MI_SPLITTER_WATCH_I: entity work.MI_SPLITTER
   generic map(
      ITEMS      => 2,
      ADDR_WIDTH => 5,
      DATA_WIDTH => 32,
      PIPE       => false
   )
   port map(
      -- Common interface
      CLK      => CLK,
      RESET    => RESET,

      -- Input MI interface
      IN_DWR   => mi32_watch_dwr,
      IN_ADDR  => mi32_watch_addr(5 downto 0),
      IN_BE    => mi32_watch_be,
      IN_RD    => mi32_watch_rd,
      IN_WR    => mi32_watch_wr,
      IN_ARDY  => mi32_watch_ardy,
      IN_DRD   => mi32_watch_drd,
      IN_DRDY  => mi32_watch_drdy,

      -- Output MI interfaces
      OUT_DWR(31 downto 0)    => mi32_rx_watch_dwr,
      OUT_DWR(63 downto 32)   => mi32_tx_watch_dwr,
      OUT_ADDR(4 downto 0)    => mi32_rx_watch_addr(4 downto 0),
      OUT_ADDR(9 downto 5)    => mi32_tx_watch_addr(4 downto 0),
      OUT_BE(3 downto 0)      => mi32_rx_watch_be,
      OUT_BE(7 downto 4)      => mi32_tx_watch_be,
      OUT_RD(0)               => mi32_rx_watch_rd,
      OUT_RD(1)               => mi32_tx_watch_rd,
      OUT_WR(0)               => mi32_rx_watch_wr,
      OUT_WR(1)               => mi32_tx_watch_wr,
      OUT_ARDY(0)             => mi32_rx_watch_ardy,
      OUT_ARDY(1)             => mi32_tx_watch_ardy,
      OUT_DRD(31 downto 0)    => mi32_rx_watch_drd,
      OUT_DRD(63 downto 32)   => mi32_tx_watch_drd,
      OUT_DRDY(0)             => mi32_rx_watch_drdy,
      OUT_DRDY(1)             => mi32_tx_watch_drdy
   );
   
   mi32_rx_watch_addr(31 downto 5) <= (others => '0');
   mi32_tx_watch_addr(31 downto 5) <= (others => '0');
   
   -- FL_WATCH RX (ibuf->application)
   FL_WATCH_RX_I : FL_WATCH_2
   port map(
      CLK       => CLK,
      RESET     => RESET,

      SOF_N     => fl_watch_rx_sof_n,
      EOF_N     => fl_watch_rx_eof_n,
      SOP_N     => fl_watch_rx_sop_n,
      EOP_N     => fl_watch_rx_eop_n,
      DST_RDY_N => fl_watch_rx_dst_rdy_n,
      SRC_RDY_N => fl_watch_rx_src_rdy_n,

      MI_DWR    => mi32_rx_watch_dwr,
      MI_ADDR   => mi32_rx_watch_addr,
      MI_RD     => mi32_rx_watch_rd,
      MI_WR     => mi32_rx_watch_wr,
      MI_BE     => mi32_rx_watch_be,
      MI_DRD    => mi32_rx_watch_drd,
      MI_ARDY   => mi32_rx_watch_ardy,
      MI_DRDY   => mi32_rx_watch_drdy
   );

   fl_watch_rx_sof_n <= IBUF1_TX_SOF_N & IBUF0_TX_SOF_N;
   fl_watch_rx_eof_n <= IBUF1_TX_EOF_N & IBUF0_TX_EOF_N;
   fl_watch_rx_sop_n <= IBUF1_TX_SOP_N & IBUF0_TX_SOP_N;
   fl_watch_rx_eop_n <= IBUF1_TX_EOP_N & IBUF0_TX_EOP_N;
   fl_watch_rx_src_rdy_n <= IBUF1_TX_SRC_RDY_N & IBUF0_TX_SRC_RDY_N;
   fl_watch_rx_dst_rdy_n <= TX1_DST_RDY_N & TX0_DST_RDY_N;

   -- FL_WATCH TX (application->obuf)
   FL_WATCH_TX_I : FL_WATCH_2
   port map(
      CLK       => CLK,
      RESET     => RESET,

      SOF_N     => fl_watch_tx_sof_n,
      EOF_N     => fl_watch_tx_eof_n,
      SOP_N     => fl_watch_tx_sop_n,
      EOP_N     => fl_watch_tx_eop_n,
      DST_RDY_N => fl_watch_tx_dst_rdy_n,
      SRC_RDY_N => fl_watch_tx_src_rdy_n,

      MI_DWR    => mi32_tx_watch_dwr,
      MI_ADDR   => mi32_tx_watch_addr,
      MI_RD     => mi32_tx_watch_rd,
      MI_WR     => mi32_tx_watch_wr,
      MI_BE     => mi32_tx_watch_be, 
      MI_DRD    => mi32_tx_watch_drd, 
      MI_ARDY   => mi32_tx_watch_ardy, 
      MI_DRDY   => mi32_tx_watch_drdy 
   );

   fl_watch_tx_sof_n <= RX1_SOF_N & RX0_SOF_N;
   fl_watch_tx_eof_n <= RX1_EOF_N & RX0_EOF_N;
   fl_watch_tx_sop_n <= RX1_SOP_N & RX0_SOP_N;
   fl_watch_tx_eop_n <= RX1_EOP_N & RX0_EOP_N;
   fl_watch_tx_src_rdy_n <= RX1_SRC_RDY_N & RX0_SRC_RDY_N;
   fl_watch_tx_dst_rdy_n <= OBUF1_RX_DST_RDY_N & OBUF0_RX_DST_RDY_N;
end generate;
NGENERATE_WATCH: if (WATCHER = false)  generate
   mi32_exp_dwr <= MI32_DWR;
   mi32_exp_addr <= MI32_ADDR;
   mi32_exp_be <= MI32_BE;
   mi32_exp_rd <= MI32_RD;
   mi32_exp_wr <= MI32_WR;
   MI32_DRD <= mi32_exp_drd;
   MI32_ARDY <= mi32_exp_ardy;
   MI32_DRDY <= mi32_exp_drdy;
end generate;

   -- Example BlockRAM memory
   RAMB18SDP_inst : RAMB18SDP
   generic map (
      DO_REG => 0,            -- Optional output register (0 or 1)
      INIT => X"000000000",   --  Initial values on output port
      SIM_COLLISION_CHECK => "ALL",
      SIM_MODE => "SAFE",
      SRVAL => X"000000000"   --  Set/Reset value for port output
      )
   port map (
      DO => bram_do,          -- 32-bit Data Output
      DOP => open,            -- 4-bit  Parity Output
      RDCLK => CLK,           -- 1-bit read port clock
      RDEN => mi32_exp_rd,    -- 1-bit read port enable
      REGCE => '1',           -- 1-bit register enable input
      SSR => '0',             -- 1-bit synchronous output set/reset input
      WRCLK => CLK,           -- 1-bit write port clock
      WREN => we_bram,        -- 1-bit write port enable
      WRADDR => mi32_exp_addr(10 downto 2), -- 9-bit write port address input
      RDADDR => mi32_exp_addr(10 downto 2), -- 9-bit read port address input
      DI => mi32_exp_dwr,     -- 32-bit data input
      DIP => "0000",          -- 4-bit parity data input
      WE => "1111"            -- 4-bit write enable input
   );

   -- Create one cycle reading latency
   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            mi32_exp_drdy <= '0';
         else
            mi32_exp_drdy <= mi32_exp_rd;
            reg_mi32_exp_addr_9 <= mi32_exp_addr(11);
         end if;
      end if;
   end process;

   mi32_exp_ardy <= mi32_exp_rd or mi32_exp_wr;

   -- Address decoder selects which register to write into
   process(mi32_exp_addr)
   begin
      cs_bram        <= '0';
      cs_experiment0 <= '0';
      cs_experiment1 <= '0';
      cs_experiment2 <= '0';
      if (mi32_exp_addr(11) = '0') then
         cs_bram     <= '1';
      else
         case mi32_exp_addr(3 downto 2) is                                                    
            when "00" => cs_experiment0 <= '1';                                           
            when "01" => cs_experiment1 <= '1';                                           
            when "10" => cs_experiment2 <= '1';                                           
            when others =>                                                                
         end case;
      end if;
   end process;

   -- Control write enable to registers
   we_bram        <= cs_bram        and mi32_exp_wr;
   we_experiment0 <= cs_experiment0 and mi32_exp_wr;
   we_experiment1 <= cs_experiment1 and mi32_exp_wr;
   we_experiment2 <= cs_experiment2 and mi32_exp_wr;

   -- Select which register to read 
   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         reg_do <= reg_experiment0;
         case mi32_exp_addr(3 downto 2) is
            when "00" => reg_do <= reg_experiment0;
            when "01" => reg_do <= reg_experiment1;
            when "10" => reg_do <= reg_experiment2;
            when others =>
         end case;
      end if;
   end process;

   -- Selects whether to read from registers or BlockRAM
   process(bram_do, reg_mi32_exp_addr_9, reg_do)
   begin
      mi32_exp_drd <= bram_do;
      if (reg_mi32_exp_addr_9 = '0') then
         mi32_exp_drd <= bram_do;
      else
         mi32_exp_drd <= reg_do;
      end if;
   end process;

   -- Read-write registers
   process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_experiment0 <= (others => '0');
            reg_experiment1 <= (others => '0');
         else
            if (we_experiment0 = '1') then
               reg_experiment0 <= mi32_exp_dwr;
            end if;
            if (we_experiment1 = '1') then
               reg_experiment1 <= mi32_exp_dwr;
            end if;
         end if;
      end if;
   end process;

   -- Read-only register (constant)
   reg_experiment2 <= X"01234567";

   -- -------------------------------------------------------------------------
   --                            Internal Bus
   -- -------------------------------------------------------------------------
   IB_ENDPOINT_I : IB_ENDPOINT_SYNTH
   port map(
      -- Common Interface
      CLK        => CLK,
      RESET      => RESET,

      -- Internal Bus Interface
      IB_DOWN_DATA        => IB_DOWN_DATA,
      IB_DOWN_SOF_N       => IB_DOWN_SOF_N,
      IB_DOWN_EOF_N       => IB_DOWN_EOF_N,
      IB_DOWN_SRC_RDY_N   => IB_DOWN_SRC_RDY_N,
      IB_DOWN_DST_RDY_N   => IB_DOWN_DST_RDY_N,
      IB_UP_DATA          => IB_UP_DATA,
      IB_UP_SOF_N         => IB_UP_SOF_N,
      IB_UP_EOF_N         => IB_UP_EOF_N,
      IB_UP_SRC_RDY_N     => IB_UP_SRC_RDY_N,
      IB_UP_DST_RDY_N     => IB_UP_DST_RDY_N,

      -- Write Interface
      WR_REQ        => ibep_wr_req,
      WR_RDY        => ibep_wr_req,
      WR_DATA       => ibep_dwr,
      WR_ADDR       => ibep_wraddr,
      WR_BE         => ibep_wr_be,
      WR_LENGTH     => open,
      WR_SOF        => open,
      WR_EOF        => open,

      -- Read Interface
      RD_REQ           => ibep_rd_req,
      RD_ARDY_ACCEPT   => ibep_rd_dst_rdy,
      RD_ADDR          => ibep_rdaddr,
      RD_BE            => open,
      RD_LENGTH        => open,
      RD_SOF           => open,
      RD_EOF           => open,
      RD_DATA          => ibep_drd,
      RD_SRC_RDY       => reg_ibep_rd_req,
      RD_DST_RDY       => ibep_rd_dst_rdy,

      -- Bus Master Interface
      BM_DATA          => X"0000000000000000",
      BM_SOF_N         => '1',
      BM_EOF_N         => '1',
      BM_SRC_RDY_N     => '1',
      BM_DST_RDY_N     => open,
      BM_TAG           => open,
      BM_TAG_VLD       => open
   );

   RAMB18SDP_inst0 : RAMB18SDP
   generic map (
      DO_REG   => 0,            -- Optional output register (0 or 1)
      INIT     => X"000000000", --  Initial values on output port
      SIM_COLLISION_CHECK => "ALL",
      SIM_MODE => "SAFE",
      SRVAL    => X"000000000"  --  Set/Reset value for port output
      )
   port map (
      DO       => ibep_drd(31 downto 0),  -- 32-bit Data Output
      DOP      => open,                   -- 4-bit  Parity Output
      RDCLK    => CLK,                    -- 1-bit read port clock
      RDEN     => ibep_rd_req,            -- 1-bit read port enable
      REGCE    => '1',                    -- 1-bit register enable input
      SSR      => '0',              -- 1-bit synchronous output set/reset input
      WRCLK    => CLK,                    -- 1-bit write port clock
      WREN     => ibep_wr_req,            -- 1-bit write port enable
      WRADDR   => ibep_wraddr(10 downto 2),-- 9-bit write port address input
      RDADDR   => ibep_rdaddr(10 downto 2),-- 9-bit read port address input
      DI       => ibep_dwr(31 downto 0),  -- 32-bit data input
      DIP      => "0000",                 -- 4-bit parity data input
      WE       => ibep_wr_be(3 downto 0)  -- 4-bit write enable input
   );

   RAMB18SDP_inst1 : RAMB18SDP
   generic map (
      DO_REG   => 0,             -- Optional output register (0 or 1)
      INIT     => X"000000000",  --  Initial values on output port
      SIM_COLLISION_CHECK => "ALL",
      SIM_MODE => "SAFE",
      SRVAL    => X"000000000"   --  Set/Reset value for port output
      )
   port map (
      DO       => ibep_drd(63 downto 32), -- 32-bit Data Output
      DOP      => open,                   -- 4-bit  Parity Output
      RDCLK    => CLK,                    -- 1-bit read port clock
      RDEN     => ibep_rd_req,            -- 1-bit read port enable
      REGCE    => '1',                    -- 1-bit register enable input
      SSR      => '0',              -- 1-bit synchronous output set/reset input
      WRCLK    => CLK,                    -- 1-bit write port clock
      WREN     => ibep_wr_req,            -- 1-bit write port enable
      WRADDR   => ibep_wraddr(10 downto 2),-- 9-bit write port address input
      RDADDR   => ibep_rdaddr(10 downto 2),-- 9-bit read port address input
      DI       => ibep_dwr(63 downto 32), -- 32-bit data input
      DIP      => "0000",                 -- 4-bit parity data input
      WE       => ibep_wr_be(7 downto 4)  -- 4-bit write enable input
   );
   
   -- Delay read request and use it as acknowledge of read data
   reg_ibep_rd_req_p : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         reg_ibep_rd_req <= ibep_rd_req;
      end if;
   end process;


   -- -------------------------------------------------------------------------
   --                              PACODAG
   -- -------------------------------------------------------------------------
   PACODAG_TOP_I: entity work.pacodag_tsu_top2_t64
   generic map(
      HEADER_EN => PACODAG_HEADER_EN,
      FOOTER_EN => PACODAG_FOOTER_EN
   )
   port map(
      -- Common interface
      RESET    => RESET,
      -- IBUF interface
      PCD0_CTRL_CLK              => IBUF0_CTRL_CLK,
      PCD0_CTRL_DATA             => IBUF0_CTRL_DATA,
      PCD0_CTRL_REM              => IBUF0_CTRL_REM,
      PCD0_CTRL_SRC_RDY_N        => IBUF0_CTRL_SRC_RDY_N,
      PCD0_CTRL_SOP_N            => IBUF0_CTRL_SOP_N,
      PCD0_CTRL_EOP_N            => IBUF0_CTRL_EOP_N,
      PCD0_CTRL_DST_RDY_N        => IBUF0_CTRL_DST_RDY_N,
      PCD0_CTRL_RDY              => IBUF0_CTRL_RDY,
      PCD0_SOP                   => IBUF0_SOP,
      PCD0_STAT_PAYLOAD_LEN      => IBUF0_PAYLOAD_LEN,
      PCD0_STAT_FRAME_ERROR      => IBUF0_FRAME_ERROR,
      PCD0_STAT_CRC_CHECK_FAILED => IBUF0_CRC_CHECK_FAILED,
      PCD0_STAT_MAC_CHECK_FAILED => IBUF0_MAC_CHECK_FAILED,
      PCD0_STAT_LEN_BELOW_MIN    => IBUF0_LEN_BELOW_MIN,
      PCD0_STAT_LEN_OVER_MTU     => IBUF0_LEN_OVER_MTU,
      PCD0_STAT_DV               => IBUF0_STAT_DV,

      PCD1_CTRL_CLK              => IBUF1_CTRL_CLK,
      PCD1_CTRL_DATA             => IBUF1_CTRL_DATA,
      PCD1_CTRL_REM              => IBUF1_CTRL_REM,
      PCD1_CTRL_SRC_RDY_N        => IBUF1_CTRL_SRC_RDY_N,
      PCD1_CTRL_SOP_N            => IBUF1_CTRL_SOP_N,
      PCD1_CTRL_EOP_N            => IBUF1_CTRL_EOP_N,
      PCD1_CTRL_DST_RDY_N        => IBUF1_CTRL_DST_RDY_N,
      PCD1_CTRL_RDY              => IBUF1_CTRL_RDY,
      PCD1_SOP                   => IBUF1_SOP,
      PCD1_STAT_PAYLOAD_LEN      => IBUF1_PAYLOAD_LEN,
      PCD1_STAT_FRAME_ERROR      => IBUF1_FRAME_ERROR,
      PCD1_STAT_CRC_CHECK_FAILED => IBUF1_CRC_CHECK_FAILED,
      PCD1_STAT_MAC_CHECK_FAILED => IBUF1_MAC_CHECK_FAILED,
      PCD1_STAT_LEN_BELOW_MIN    => IBUF1_LEN_BELOW_MIN,
      PCD1_STAT_LEN_OVER_MTU     => IBUF1_LEN_OVER_MTU,
      PCD1_STAT_DV               => IBUF1_STAT_DV,

      TS       => ts_sync,
      TS_DV    => ts_dv_sync
   );

   -- ---------------------------------------------------------------
   -- Generate tsu_async only if timestamp unit is also generated
   ts_true_async : if TIMESTAMP_UNIT = true generate
      tsu_async_i : tsu_async
      -- PORTS
      port map (
         RESET          => RESET,

         -- Input interface
         IN_CLK         => TS_CLK,

         IN_TS          => TS,
         IN_TS_DV       => TS_DV,

         -- Output interface
         OUT_CLK        => IBUF0_CTRL_CLK,

         OUT_TS         => ts_sync,
         OUT_TS_DV      => ts_dv_sync
      );
   end generate ts_true_async;

   -- Else map TS and TS_DV signals directly into pacodag
   ts_false_async : if TIMESTAMP_UNIT = false generate
      ts_sync <= TS;
      ts_dv_sync <= TS_DV;
   end generate ts_false_async;
   -- ---------------------------------------------------------------

end architecture full;
