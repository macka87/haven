-- rx_opt_tb.vhd: Testbench File
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

use work.ib_pkg.all; -- Internal Bus Package
use work.lb_pkg.all; -- Local Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.ib_bfm_pkg.all; -- Internal Bus BFM Package
use work.math_pack.all;

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
   constant CLKPER      : time := 10 ns;
   constant miclkper    : time := 10 ns;
   constant gndvec      : std_logic_vector(128 downto 0) := (others => '0');
   constant BUFFER_ADDR       : std_logic_vector(31 downto 0) := X"00200000";
   constant BUFFER_SIZE       : integer := 1024;
   constant DMA_DATA_WIDTH    : integer := 16;

   constant TEST_LIMIT           : std_logic_vector(31 downto 0) := X"04000000";
   constant IB2LB_BASE_ADDR      : std_logic_vector(31 downto 0) := X"00002000";
   constant IB2LB_LIMIT          : std_logic_vector(31 downto 0) := X"04000000";
   signal CLK          : std_logic;
   signal RESET        : std_logic;
   signal mi_clk       : std_logic;

   signal interrupt   : std_logic;
   signal enable      : std_logic;

   -- Receive buffer interface
   signal buf_newlen       : std_logic_vector(15 downto 0);
   signal buf_newlen_dv    : std_logic;
   signal buf_newlen_rdy   : std_logic;
   signal buf_rellen       : std_logic_vector(15 downto 0);
   signal buf_rellen_dv    : std_logic;

   -- Descriptor FIFO interface
   signal desc_read   : std_logic;
   signal desc_do     : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal desc_empty  : std_logic;

   -- DMA Interface
   signal dma_addr    : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal dma_dout    : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal dma_req     : std_logic;
   signal dma_ack     : std_logic;
   signal dma_done    : std_logic;
   signal dma_tag     : std_logic_vector(15 downto 0);

   signal internal_bus        : t_internal_bus64;

   -- endpoint Map
   signal ib_wr               : t_ibmi_write64;
   signal ib_rd               : t_ibmi_read64s;
   signal ib_bm               : t_ibbm_64;
   signal lbus0               : t_local_bus16; 
  
   alias ib_clk               : std_logic is CLK; 

   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;
   
   signal mi                 :t_mi32;


begin

-- ------------------------------------------------------------------
-- UUT Instantion
uut : entity work.rx_dma_ctrl_opt
   generic map(
      BUFFER_ADDR    => BUFFER_ADDR,
      BUFFER_SIZE    => BUFFER_SIZE,
      DMA_DATA_WIDTH => DMA_DATA_WIDTH,
      DMA_TAG_ID     => X"20"
   )
   port map(
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
      INTERRUPT   => interrupt,
      ENABLE      => enable,

      -- Receive buffer interface
      BUF_NEWLEN       => buf_newlen,
      BUF_NEWLEN_DV    => buf_newlen_dv,
      BUF_NEWLEN_RDY   => buf_newlen_rdy,
      BUF_RELLEN       => buf_rellen,
      BUF_RELLEN_DV    => buf_rellen_dv,

      -- Descriptor FIFO interface
      DESC_READ   => desc_read,
      DESC_DO     => desc_do,
      DESC_EMPTY  => desc_empty,

      -- Memory interface
      SW_DWR      => mi.dwr,
      SW_ADDR     => mi.addr(5 downto 0),
      SW_RD       => mi.rd,
      SW_WR       => mi.wr,
      SW_BE       => mi.be,
      SW_DRD      => mi.drd,
      SW_ARDY     => mi.ardy,
      SW_DRDY     => mi.drdy,
      -- DMA Interface
      DMA_ADDR    => dma_addr,
      DMA_DOUT    => dma_dout,
      DMA_REQ     => dma_req,
      DMA_ACK     => dma_ack,
      DMA_DONE    => dma_done,
      DMA_TAG     => dma_tag 
   );
   
DMA2BM_I : entity work.DMA2BM
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,

      -- DMA Interface
      DMA_ADDR    => dma_addr,
      DMA_DOUT    => dma_dout,
      DMA_REQ     => dma_req,
      DMA_ACK     => dma_ack,
      DMA_DONE    => dma_done,
      DMA_TAG     => dma_tag,

      -- Bus master interface
      BM_GLOBAL_ADDR => ib_bm.GLOBAL_ADDR,
      BM_LOCAL_ADDR  => ib_bm.LOCAL_ADDR,
      BM_LENGTH      => ib_bm.LENGTH,
      BM_TAG         => ib_bm.TAG,
      BM_TRANS_TYPE  => ib_bm.TRANS_TYPE,
      BM_REQ         => ib_bm.REQ,
      BM_ACK         => ib_bm.ACK,
      BM_OP_TAG      => ib_bm.OP_TAG,
      BM_OP_DONE     => ib_bm.OP_DONE
   );

-- clk clock generator
clkgen_CLK: process
begin
   CLK <= '1';
   wait for CLKPER/2;
   CLK <= '0';
   wait for CLKPER/2;
end process;

-- ----------------------------------------------------
-- MI clock generator
clkgen_mi : process
begin
   mi_clk <= '1';
   wait for miclkper/2;
   mi_clk <= '0';
   wait for miclkper/2;
end process;


-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT_MASTER
   generic map(
      LIMIT         => TEST_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => internal_bus,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd,

      -- Busmaster
      BM            => ib_bm
   );

-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   GENERIC MAP (
       MEMORY_SIZE => 4096,
       MEMORY_BASE_ADDR => X"00000000" & X"00000000"
       )
   PORT MAP (
      CLK          => ib_clk,
      -- Internal Bus Interface
      IB           => internal_bus
      );

-- -------------------------------------------------------------------------
--                   MI32 Simulation Component
-- -------------------------------------------------------------------------
mi32_sim: entity work.mi32_sim
   generic map (
      UPSTREAM_LOG_FILE   => "./mi32.upstream",
      DOWNSTREAM_LOG_FILE => "./mi32.downstream",
      BASE_ADDR           => X"00000000",
      LIMIT               => X"00004000",
      FREQUENCY           => LOCAL_BUS_FREQUENCY,
      BUFFER_EN           => false
   )
   port map (
      -- Common interface
      IB_RESET            => reset,
      IB_CLK              => ib_clk,

      -- User Component Interface
      CLK                 => mi_clk,
      MI32                => mi,

      -- IB SIM interface
      STATUS              => open,
      CTRL                => mi32_sim_ctrl,
      STROBE              => mi32_sim_strobe,
      BUSY                => mi32_sim_busy
   );
-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------

desc_empty     <= not enable;
ib_wr.rdy      <= '1';
ib_rd.src_rdy  <= ib_rd.dst_rdy;
ib_rd.ardy     <= ib_rd.req;
ib_rd.data     <= X"BEEF0000" & X"DEAD0000";

tb : process
   -- ----------------------------------------------------------------
   --                    Procedures declaration
   -- ----------------------------------------------------------------

   -- This procedure must be placed in this testbench file. Using this
   -- procedure is necessary for correct function of MI32_SIM
   procedure ib_op(ctrl : in t_ib_ctrl) is
   begin
      wait until (mi_clk'event and mi_clk='1' and mi32_sim_busy = '0');
      mi32_sim_ctrl <= ctrl;
      mi32_sim_strobe <= '1';
      wait until (mi_clk'event and mi_clk='1');
      mi32_sim_strobe <= '0';
   end ib_op;


begin
   RESET <= '1', '0' after 100 ns;

   wait for 500 ns;

   buf_newlen     <= X"0000";
   buf_newlen_dv  <= '0';
   desc_do        <= gndvec(DMA_DATA_WIDTH - 1 downto 0);

   InitMemory(256, "rx_desc_data.txt", IbCmd);
--    ShowMemory(IbCmd);

   
   -- inicialization
   -- initialization - Write swBuffSizeMask 
   ib_op(ib_local_write(X"00000010", X"11111111", 4, 16#ABAB#, '0', X"00000000" & X"000003FF"));
   -- initialization - Write start command to controlRegiter 
   ib_op(ib_local_write(X"00000000", X"11111111", 4, 16#ABAB#, '0', X"00000000" & X"00000001"));

   buf_newlen     <= X"0080";
   buf_newlen_dv  <= '1';
   wait for CLKPER;
   buf_newlen_dv  <= '0';

   wait for 240*CLKPER;
   buf_newlen     <= X"0100";
   buf_newlen_dv  <= '1';
   wait for CLKPER;
   buf_newlen_dv  <= '0';


   wait;

end process;


end architecture behavioral;
-- ----------------------------------------------------------------------------

