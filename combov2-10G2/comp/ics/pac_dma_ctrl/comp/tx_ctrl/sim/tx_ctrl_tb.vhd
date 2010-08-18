-- tx_ctrl_tb.vhd: Tx packet dma controller Testbench File
-- Copyright (C) 2009 CESNET
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
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use ieee.numeric_std.all;

-- package with IB records
use work.ib_pkg.all;
-- ib_sim package
use work.ib_sim_oper.all;
use work.math_pack.all;
use work.ib_bfm_pkg.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant gndvec      : std_logic_vector(128 downto 0) := (others => '0');
   constant CLKPER      : time := 10 ns;
   constant BUFFER_ADDR : std_logic_vector := X"00010000";
   constant BUFFER_GAP  : std_logic_vector := X"00008000";
   constant BUFFER_SIZE : integer := 4096;
   constant CHANNELS    : integer := 4;
   constant DMA_DATA_WIDTH : integer := 32;
   constant DMA_ID      : std_logic_vector := "11";
   constant NUM_FLAGS   : integer := 8;

   constant IB_EP_LIMIT : std_logic_vector(31 downto 0) := X"00200000";

   signal CLK           : std_logic;
   signal RESET         : std_logic;
   alias  ib_clk        : std_logic is CLK;
   signal internal_bus  : t_internal_bus64;
   signal ib_wr         : t_ibmi_write64;
   signal ib_rd         : t_ibmi_read64s;
   signal ib_bm         : t_ibbm_64;

   signal run           : std_logic_vector(CHANNELS-1 downto 0);
   signal idle          : std_logic_vector(CHANNELS-1 downto 0);

   signal su_addr       : std_logic_vector(abs(log2(CHANNELS)-1) downto 0);
   signal su_data       : std_logic_vector(NUM_FLAGS-1 downto 0);
   signal su_data_vld   : std_logic;
   signal su_hfull      : std_logic_vector(CHANNELS-1 downto 0);

     -- Rx nfifo to rx_dma_ctrl
   signal desc_dout     : std_logic_vector(63 downto 0);
   signal desc_dout_vld : std_logic;
   signal desc_raddr    : std_logic_vector(abs(log2(CHANNELS)-1) downto 0);
   signal desc_rd       : std_logic;
   signal desc_empty    : std_logic_vector(CHANNELS-1 downto 0);

   signal buf_newlen     : std_logic_vector(CHANNELS*16-1 downto 0);
   signal buf_newlen_dv  : std_logic_vector(CHANNELS-1 downto 0);
   signal buf_newlen_rdy : std_logic_vector(CHANNELS-1 downto 0);
   signal buf_rellen     : std_logic_vector(CHANNELS*16-1 downto 0);
   signal buf_rellen_dv  : std_logic_vector(CHANNELS-1 downto 0);

   signal dma_addr      : std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal dma_dout      : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal dma_req       : std_logic;
   signal dma_ack       : std_logic;
   signal dma_done      : std_logic;
   signal dma_tag       : std_logic_vector(15 downto 0);

   begin

-- ------------------------------------------------------------------
-- UUT Instantion
uut : entity work.tx_ctrl
   generic map (
      BUFFER_ADDR    => BUFFER_ADDR,
      BUFFER_GAP     => BUFFER_GAP,
      BUFFER_SIZE    => BUFFER_SIZE,
      DMA_ID         => DMA_ID,
      DMA_DATA_WIDTH => DMA_DATA_WIDTH,
      CHANNELS       => CHANNELS
   )
   port map (
      -- Common signals
      CLK      => CLK,
      RESET    => RESET,

      -- control interface
      RUN            => run,
      IDLE           => idle,

      -- Receive buffer interface
      BUF_NEWLEN     => buf_newlen,
      BUF_NEWLEN_DV  => buf_newlen_dv,
      BUF_NEWLEN_RDY => buf_newlen_rdy,
      BUF_RELLEN     => buf_rellen,
      BUF_RELLEN_DV  => buf_rellen_dv,

      -- descriptors from ddm
      DESC_READ      => desc_rd,
      DESC_ADDR      => desc_raddr,
      DESC_DO        => desc_dout,
      DESC_DO_VLD    => desc_dout_vld,
      DESC_EMPTY     => desc_empty,
 
       -- BM interface
      -- Memory interface
      DMA_ADDR        => dma_addr,
      DMA_DOUT        => dma_dout,
      DMA_REQ         => dma_req,
      DMA_ACK         => dma_ack,
      DMA_DONE        => dma_done,
      DMA_TAG         => dma_tag,

      -- status update
      SU_ADDR        => su_addr,
      SU_DATA        => su_data,
      SU_DATA_VLD    => su_data_vld,
      SU_HFULL       => su_hfull

   );

   DMA2BM_U: entity work.DMA2BM
   generic map (
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      -- Memory interface
      DMA_ADDR        => dma_addr,
      DMA_DOUT        => dma_dout,
      DMA_REQ         => dma_req,
      DMA_ACK         => dma_ack,
      DMA_DONE        => dma_done,
      DMA_TAG         => dma_tag,

      -- Bus master interface
      BM_GLOBAL_ADDR  => ib_bm.global_addr,
      BM_LOCAL_ADDR   => ib_bm.local_addr,
      BM_LENGTH       => ib_bm.length,
      BM_TAG          => ib_bm.tag,
      bM_TRANS_TYPE   => ib_bm.trans_type,
      BM_REQ          => ib_bm.req,
      bM_ACK          => ib_bm.ack,
      -- Output
      BM_OP_TAG       => ib_bm.op_tag,
      BM_OP_DONE      => ib_bm.op_done

   );


-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   generic map (
       MEMORY_SIZE => 1024,
       MEMORY_BASE_ADDR => X"0000DEAD" & X"00000000"
   )
   port map (
      CLK          => ib_clk,
      -- Internal Bus Interface
      IB           => internal_bus
   );

-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT_MASTER
   generic map(
      LIMIT         => IB_EP_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => RESET,
      -- Internal Bus Interface
      INTERNAL_BUS  => internal_bus,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd,

      -- Busmaster
      BM            => ib_bm
   );

-- clk clock generator
clkgen_CLK: process
begin
   CLK <= '1';
   wait for CLKPER/2;
   CLK <= '0';
   wait for CLKPER/2;
end process;

-- process to simulate rx buffer
ib_wr.RDY      <= '1';
buf_newlen_rdy <= not gndvec(CHANNELS-1 downto 0);
su_hfull       <= gndvec(CHANNELS-1 downto 0);

new_descp: process
begin
   desc_dout_vld  <= '0';
   desc_dout <= X"0000000000000000";
   wait until desc_rd = '1' and RESET = '0';
   wait for CLKPER;
   wait for CLKPER;
   desc_dout_vld  <= '1';
   desc_dout <= X"0000000300000076";
   wait for CLKPER;
   desc_dout_vld  <= '0';
   wait until desc_rd = '1';
   wait for CLKPER;
   wait for CLKPER;
   desc_dout_vld  <= '1';
   desc_dout <= X"0000DEAD" & X"00000000";
   wait for CLKPER;
   desc_dout_vld  <= '0';
   wait for CLKPER;
end process; 

buf_rellen     <= gndvec(63 downto 16) & X"0080";
rel_packet: process
begin
   buf_rellen_dv  <= "0000";
   wait until buf_newlen_dv = "0001";
   wait for 2*CLKPER;
   buf_rellen_dv  <= "0001";
   wait for CLKPER;
end process; 

run <= (others => '1');
-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------
-- ----------------------------------------------------------------
begin
   InitMemory(256, "desc_data.txt", IbCmd);
   desc_empty     <= "1111";

   RESET <= '1', '0' after 100 ns;

   wait for 15*CLKPER;
   desc_empty     <= "1110";
   wait;
end process;


end architecture behavioral;
