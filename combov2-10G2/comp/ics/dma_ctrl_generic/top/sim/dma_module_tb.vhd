-- dma_module_tb.vhd: Testbench File
-- Copyright (C) 2009 CESNET
-- Author: Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;

use work.math_pack.all;
use std.textio.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

use work.ib_pkg.all;
use work.ib_sim_oper.all;
use work.ib_bfm_pkg.all;

use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- Constant declaration
   constant CLKPER            : time    := 10 ns;
   constant DMA_IFC_COUNT     : integer := 4;
   constant DATA_WIDTH        : integer := 16;

   constant BUFFER_ADDR       : std_logic_vector(31 downto 0) := X"02000000";
   constant DESC_BASE_ADDR    : std_logic_vector(31 downto 0) := X"02200000";

   constant DESC_MAN_INIT_BIT_POS : integer := 18;
   constant DESC_MAN_INIT_PHASE_OFFSET : std_logic_vector(31 downto 0) := conv_std_logic_vector(2**DESC_MAN_INIT_BIT_POS, 32);
   constant DESC_INIT_ADDR    : std_logic_vector(31 downto 0) := X"02200000" + DESC_MAN_INIT_PHASE_OFFSET;

   signal CLK                 : std_logic;
   signal RESET               : std_logic;

   -- input FrameLink interface
   signal RX_SOF_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_SOP_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_EOP_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_EOF_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_SRC_RDY_N        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_DST_RDY_N        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RX_DATA             : std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
   signal RX_REM              : std_logic_vector(DMA_IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
   -- output FrameLink interface
   signal TX_SOF_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_SOP_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_EOP_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_EOF_N            : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_SRC_RDY_N        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_DST_RDY_N        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TX_DATA             : std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
   signal TX_REM              : std_logic_vector(DMA_IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
  
   signal FL_SIM_CTRL0        : work.fl_sim_oper.t_fl_ctrl;
   signal FL_SIM_STROBE0      : std_logic;
   signal FL_SIM_BUSY0        : std_logic;
   signal FL_SIM_CTRL1        : work.fl_sim_oper.t_fl_ctrl;
   signal FL_SIM_STROBE1      : std_logic;
   signal FL_SIM_BUSY1        : std_logic;

   signal IB                  : t_internal_bus64;
   signal IB_lb               : t_internal_bus64;
   signal IB_dma              : t_internal_bus64;
   signal LB                  : t_local_bus16;

   signal ib_sim_STATUS       : t_ib_status;
   signal ib_sim_CTRL         : t_ib_ctrl;
   signal ib_sim_STROBE       : std_logic;
   signal ib_sim_BUSY         : std_logic;

begin
   
-- ------------------------------------------------------------------
-- UUT Instantion
   uut : entity work.dma_module
   generic map(
      BUFFER_ADDR       => BUFFER_ADDR,
      DESC_BASE_ADDR    => DESC_BASE_ADDR,

      IB_EP_LIMIT       => X"10000000",
      LB_EP_BASE_ADDR   => X"00000000",
      LB_EP_LIMIT       => X"00000800",
      
      DMA_IFC_COUNT     => DMA_IFC_COUNT,
      DATA_WIDTH        => DATA_WIDTH
      )
   port map(
      -- Common interface
      CLK               => CLK,
      RESET             => RESET,
      -- input FrameLink interface
      RX_SOF_N          => TX_SOF_N,
      RX_SOP_N          => TX_SOP_N,
      RX_EOP_N          => TX_EOP_N,
      RX_EOF_N          => TX_EOF_N,
      RX_SRC_RDY_N      => TX_SRC_RDY_N,
      RX_DST_RDY_N      => TX_DST_RDY_N,
      RX_DATA           => TX_DATA,
      RX_REM            => TX_REM,
      -- output FrameLink interface
      TX_SOF_N          => RX_SOF_N,
      TX_SOP_N          => RX_SOP_N,
      TX_EOP_N          => RX_EOP_N,
      TX_EOF_N          => RX_EOF_N,
      TX_SRC_RDY_N      => RX_SRC_RDY_N,
      TX_DST_RDY_N      => RX_DST_RDY_N,
      TX_DATA           => RX_DATA,
      TX_REM            => RX_REM,

      IB                => IB_dma,
      LB                => LB
   );

   fl_gen: for i in 0 to DMA_IFC_COUNT-1 generate
      FL_BFM_U1 : entity work.FL_BFM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         FL_BFM_ID      => i
      )
      port map (
         RESET          => reset,
         CLK            => clk,

         TX_DATA        => TX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
         TX_REM         => TX_REM((i+1)*log2(DATA_WIDTH/8)-1 downto i*log2(DATA_WIDTH/8)),
         TX_SOF_N       => TX_SOF_N(i),
         TX_EOF_N       => TX_EOF_N(i),
         TX_SOP_N       => TX_SOP_N(i),
         TX_EOP_N       => TX_EOP_N(i),
         TX_SRC_RDY_N   => TX_SRC_RDY_N(i),
         TX_DST_RDY_N   => TX_DST_RDY_N(i)
        );     

      MONITOR_I1: entity work.MONITOR
      generic map(
         RX_TX_DATA_WIDTH => DATA_WIDTH,
         FILE_NAME      => "./logs/monitor" & character'val(character'pos('0') + i) & ".txt",
         FRAME_PARTS    => 3,
         RDY_DRIVER     => RND
      )
      port map(
         FL_RESET       => reset,
         FL_CLK         => clk,

         RX_DATA        => RX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
         RX_REM         => RX_REM((i+1)*log2(DATA_WIDTH/8)-1 downto i*log2(DATA_WIDTH/8)),
         RX_SOF_N       => RX_SOF_N(i),
         RX_EOF_N       => RX_EOF_N(i),
         RX_SOP_N       => RX_SOP_N(i),
         RX_EOP_N       => RX_EOP_N(i),
         RX_SRC_RDY_N   => RX_SRC_RDY_N(i),
         RX_DST_RDY_N   => RX_DST_RDY_N(i)
        );
   end generate;

   IB_SWITCH0_I: entity work.IB_SWITCH
   generic map(
      DATA_WIDTH        => 64,
      SWITCH_BASE       => X"00000000",
      SWITCH_LIMIT      => X"C4000000",
      DOWNSTREAM0_BASE  => X"00000000",
      DOWNSTREAM0_LIMIT => X"02000000",
      DOWNSTREAM1_BASE  => X"02000000",
      DOWNSTREAM1_LIMIT => X"C2000000"
   )
   port map(
      IB_CLK            => CLK,
      IB_RESET          => RESET,
      PORT0             => IB,
      PORT1             => ib_lb,
      PORT2             => ib_dma
   ); 
   
   IB2LB_I: entity work.LB_ROOT
   generic map(
      BASE_ADDR         => X"00000000",
      LIMIT             => X"02000000"
   )
   port map(
      IB_CLK            => CLK,
      RESET             => RESET,
      INTERNAL_BUS      => ib_lb,
      LOCAL_BUS         => lb
   ); 

   IB_BFM_U : entity work.IB_BFM
   GENERIC MAP (
      MEMORY_SIZE       => 16#94000#,
      MEMORY_BASE_ADDR  => X"00000000" & X"00000000"
       )
   PORT MAP (
      CLK               => CLK,
      IB                => IB
   );

-- clk clock generator
clkgen_CLK: process
begin
   CLK <= '1';
   wait for CLKPER/2;
   CLK <= '0';
   wait for CLKPER/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb: process
   variable tx_current_sw_end_ptr : integer := 0;
begin
   RESET <= '1', '0' after 50 ns;
   wait for 100 ns;

   -- Initialize RX0/TX0 descriptors (BUG in IB_BFM InitHostMemory)
   InitMemoryFromAddr(16#1000#, 16#10000#, "./tests/rx0_desc_data.txt", IbCmd);
   InitMemoryFromAddr(16#1000#, 16#11000#, "./tests/tx0_desc_data.txt", IbCmd);
   -- Initialize RX/TX descriptors list (for IFC 1, 2, 3)
   InitMemoryFromAddr(16#1000#, 16#92000#, "./tests/rx1_desc_data.txt", IbCmd);
   InitMemoryFromAddr(16#1000#, 16#93000#, "./tests/tx1_desc_data.txt", IbCmd);
   -- Initialize TX MEM
   InitMemoryFromAddr(16#1000#, 16#52000#,"./tests/dump", IbCmd);

   -- Initialize descriptor manager
   -------------------------------------------------------------------
   -- write address of first desc for channel 0 -- RX0
   SendLocalWrite(DESC_INIT_ADDR + 16#00# , X"08000000", 4, 16#1234#, X"00000000" & X"00010000", IbCmd);
   SendLocalWrite(DESC_INIT_ADDR + 16#04# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   -- write address of first desc for channel 1 -- TX0
   SendLocalWrite(DESC_INIT_ADDR + 16#08# , X"08000000", 4, 16#1234#, X"00000000" & X"00011000", IbCmd);
   SendLocalWrite(DESC_INIT_ADDR + 16#0C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   -- write address of first desc for channel 2 -- RX1
--   SendLocalWrite(DESC_INIT_ADDR + 16#10# , X"08000000", 4, 16#1234#, X"00000000" & X"00092000", IbCmd);
--   SendLocalWrite(DESC_INIT_ADDR + 16#14# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);
   -- write address of first desc for channel 3 -- TX1
--   SendLocalWrite(DESC_INIT_ADDR + 16#18# , X"08000000", 4, 16#1234#, X"00000000" & X"00093000", IbCmd);
--   SendLocalWrite(DESC_INIT_ADDR + 16#1C# , X"08000000", 4, 16#1234#, X"00000000" & X"00000000", IbCmd);

   -- Initialize RX and TX DMA_CTRLs
   -------------------------------------------------------------------
   -- RX0 init
   SendLocalWrite(X"00000010", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);
   -- TX0 init
   SendLocalWrite(X"00000050", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
   SendLocalWrite(X"00000040", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);
   -- RX1 init
--   SendLocalWrite(X"00000090", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
--   SendLocalWrite(X"00000080", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);
   -- TX1 init
--   SendLocalWrite(X"000000D0", X"08000000", 4, 16#1234#, X"00000000" & X"0000FFFF", IbCmd);
--   SendLocalWrite(X"000000C0", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);

   -- page break test                                       -- (28+32)*128 = 7680
--   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000004", IbCmd);
--   for i in 0 to 27 loop
--      SendWriteFile("./tests/fl_sim.txt", RND, flCmd_0, 0); -- 28*128 = 3584
--   end loop;
--   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);
--   wait for 20 us;
--   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000004", IbCmd);
--   for i in 0 to 31 loop
--      SendWriteFile("./tests/fl_sim.txt", RND, flCmd_0, 0); -- 32*128 = 4096
--   end loop;
--   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd);

   -- interrupt test
   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000004", IbCmd);
--   for i in 0 to 15 loop
      SendWriteFile("./tests/fl_sim.txt", RND, flCmd_0, 0);
--   end loop;
   SendLocalWrite(X"00000000", X"08000000", 4, 16#1234#, X"00000000" & X"00000002", IbCmd); 
   SendLocalWrite(X"00000018", X"08000000", 4, 16#1234#, X"00000000" & X"00000020", IbCmd);
   SendLocalWrite(X"00000014", X"08000000", 4, 16#1234#, X"00000000" & X"000000F1", IbCmd);
   SendWriteFile("./tests/fl_sim.txt", RND, flCmd_0, 0);

   -- TX test
   tx_current_sw_end_ptr := 16#10e8#;
   SendLocalWrite(X"00000058", X"08000000", 4, 16#1234#, X"00000000" & X"00000400", IbCmd);
   SendLocalWrite(X"00000054", X"08000000", 4, 16#1234#, X"00000000" & X"00002003", IbCmd);
-- SendLocalWrite(X"00000054", X"08000000", 4, 16#1234#, X"00000000" & X"00001003", IbCmd);
   SendLocalWrite(X"0000004C", X"08000000", 4, 16#1234#, X"00000000" & conv_std_logic_vector(tx_current_sw_end_ptr, 32), IbCmd);

   wait for 40 us;
   
   SendLocalRead(X"02280008", X"08000000", 4, 16#1234#, IbCmd);
   SendLocalRead(X"02280000", X"08000000", 4, 16#1234#, IbCmd);

   wait;
end process;

end architecture behavioral;
-- ----------------------------------------------------------------------------

