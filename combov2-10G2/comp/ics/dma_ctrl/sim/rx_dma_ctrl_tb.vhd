-- rx_dma_ctrl_tb.vhd: Testbench File
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

use work.ib_pkg.all; -- Internal Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package
use work.ib_bfm_pkg.all; -- Internal Bus BFM Package

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
   constant gndvec      : std_logic_vector(128 downto 0) := (others => '0');
   constant MEM_PAGE_SIZE     : integer := 4096;
   constant DESC_BLOCK_SIZE   : integer := 4096;
   constant INT_TIMEOUT       : integer := 1000;
   constant BUFFER_ADDR       : std_logic_vector(31 downto 0) := X"00001000";
   constant BUFFER_SIZE       : integer := 1024;

   constant TEST_BASE_ADDR       : integer := 16#0#;
   constant TEST_LIMIT           : std_logic_vector(31 downto 0) := X"00200000";

   signal CLK          : std_logic;
   signal RESET        : std_logic;

   -- Common interface
   signal interrupt   : std_logic_vector(1 downto 0);

   -- Receive buffer interface
   signal buf_newlen       : std_logic_vector(15 downto 0);
   signal buf_newlen_dv    : std_logic;
   signal buf_newlen_rdy   : std_logic;
   signal buf_rellen       : std_logic_vector(15 downto 0);
   signal buf_rellen_dv    : std_logic;


   -- Switch1 Map
   signal internal_bus        : t_internal_bus64;
   signal switch1_port1       : t_internal_bus64;
   signal switch1_port2       : t_internal_bus64;

   -- endpoint Map
   signal ib_wr               : t_ibmi_write64;
   signal ib_rd               : t_ibmi_read64s;
   signal ib_bm1              : t_ibbm_64;
   signal ib_bm2              : t_ibbm_64;
  
   -- IB_SIM component ctrl      
   signal ib_sim_ctrl         : t_ib_ctrl;
   signal ib_sim_strobe       : std_logic;
   signal ib_sim_busy         : std_logic;

   alias ib_clk               : std_logic is CLK; 
   signal bm1_trans_type      : std_logic_vector(3 downto 0);
   signal bm2_trans_type      : std_logic_vector(3 downto 0);

begin

-- ------------------------------------------------------------------
-- UUT Instantion
uut : entity work.rx_dma_ctrl_arch
   port map (
      -- Common interface
      PIN_CLK         => CLK,
      PIN_RESET       => RESET,
      INTERRUPT   => interrupt,

      -- Receive buffer interface
      BUF_NEWLEN       => buf_newlen,
      BUF_NEWLEN_DV    => buf_newlen_dv,
      BUF_NEWLEN_RDY   => buf_newlen_rdy,
      BUF_RELLEN       => buf_rellen,
      BUF_RELLEN_DV    => buf_rellen_dv,

      -- Memory interface
      -- Write interface
      WR_ADDR     => ib_wr.ADDR,
      WR_DATA     => ib_wr.DATA,
      WR_BE       => ib_wr.BE,
      WR_REQ      => ib_wr.REQ,
      WR_RDY      => ib_wr.RDY,
      -- Read interface
      RD_ADDR     => ib_rd.ADDR,
      RD_BE       => ib_rd.BE,
      RD_REQ      => ib_rd.REQ,
      RD_ARDY     => ib_rd.ARDY,
      RD_DATA     => ib_rd.DATA,
      RD_SRC_RDY  => ib_rd.SRC_RDY,
      RD_DST_RDY  => ib_rd.DST_RDY,

      -- Busmaster interface
      -- P1
      -- Input
      BM1_GLOBAL_ADDR => ib_bm1.GLOBAL_ADDR,
      BM1_LOCAL_ADDR  => ib_bm1.LOCAL_ADDR,
      BM1_LENGTH      => ib_bm1.LENGTH,
      BM1_TAG         => ib_bm1.TAG,
      BM1_TRANS_TYPE  => bm1_trans_type,
      BM1_REQ         => ib_bm1.REQ,
      -- Output
      BM1_ACK         => ib_bm1.ACK,
      BM1_OP_TAG      => ib_bm1.OP_TAG,
      BM1_OP_DONE     => ib_bm1.OP_DONE,

      -- P2
      -- Input
      BM2_GLOBAL_ADDR => ib_bm2.GLOBAL_ADDR,
      BM2_LOCAL_ADDR  => ib_bm2.LOCAL_ADDR,
      BM2_LENGTH      => ib_bm2.LENGTH,
      BM2_TAG         => ib_bm2.TAG,
      BM2_TRANS_TYPE  => bm2_trans_type,
      BM2_REQ         => ib_bm2.REQ,
      -- Output
      BM2_ACK         => ib_bm2.ACK,
      BM2_OP_TAG      => ib_bm2.OP_TAG,
      BM2_OP_DONE     => ib_bm2.OP_DONE

   );

ib_bm1.TRANS_TYPE <= bm1_trans_type(1 downto 0); -- two bits are unused
ib_bm2.TRANS_TYPE <= bm2_trans_type(1 downto 0);

-- clk clock generator
clkgen_CLK: process
begin
   CLK <= '1';
   wait for CLKPER/2;
   CLK <= '0';
   wait for CLKPER/2;
end process;

ib_rd.ardy <= '1';

-- Internal Bus Switch -----------------------------------------------------
IB_SWITCH1_I : entity work.IB_SWITCH
   generic map (
      -- Data Width (64/128)
      DATA_WIDTH        => 64,
      -- Port 0 Address Space
      SWITCH_BASE        => X"00000000",
      SWITCH_LIMIT       => X"01000000",
      -- Port 1 Address Space
      DOWNSTREAM0_BASE   => X"00000000",
      DOWNSTREAM0_LIMIT  => X"00400000",
      -- Port 2 Address Space
      DOWNSTREAM1_BASE   => X"00800000",
      DOWNSTREAM1_LIMIT  => X"00000100"
   )

   port map (
      -- Common Interface
      IB_CLK         => ib_clk,
      IB_RESET       => reset,
      -- Upstream Port
      PORT0          => internal_bus,
      -- Downstream Ports
      PORT1          => switch1_port1,
      PORT2          => switch1_port2
   );
   
-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT_MASTER
   generic map(
--       BASE_ADDR     => conv_std_logic_vector(TEST_BASE_ADDR, 32),
      LIMIT         => TEST_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => switch1_port1,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd,

      -- Busmaster
      BM            => ib_bm1
   );

-- -- Internal Bus simulation component ---------------------------------------
-- IB_SIM_I : entity work.IB_SIM
--    generic map (
--       UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
--       DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt"
--    )
--    port map (
--       -- Common interface
--       IB_RESET           => reset,
--       IB_CLK             => ib_clk,
-- 
--       -- Internal Bus Interface
--       INTERNAL_BUS       => internal_bus,
-- 
--       -- IB SIM interface
--       CTRL               => ib_sim_ctrl,
--       STROBE             => ib_sim_strobe,
--       BUSY               => ib_sim_busy
--       );

-- Internal Bus Bus Functional Model ------------------------------------------
IB_BFM_U : entity work.IB_BFM
   GENERIC MAP (
       MEMORY_SIZE => 1024,
       MEMORY_BASE_ADDR => X"0000DEAD" & X"00000000"
       )
   PORT MAP (
      CLK          => ib_clk,
      -- Internal Bus Interface
      IB           => internal_bus
      );

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

 -- Support for ib_op
   procedure ib_op(ctrl : in t_ib_ctrl) is
   begin
      wait until (IB_CLK'event and IB_CLK='1' and ib_sim_busy = '0');
      ib_sim_ctrl <= ctrl;
      ib_sim_strobe <= '1';
      wait until (IB_CLK'event and IB_CLK='1');
      ib_sim_strobe <= '0';
   end ib_op;


begin
   RESET <= '1', '0' after 100 ns;

   buf_newlen <= X"0000";
   buf_newlen_dv <= '0';

   InitMemory(256, "rx_desc_data.txt", IbCmd);
--    ShowMemory(IbCmd);

   wait for 300 ns;
   
   -- Write first descriptor -- initialization
--    SendLocalRead(X"00010000", X"08000000", 8, 16#1234#, IbCmd);
   SendLocalWrite(X"00010000", X"08000000", 8, 16#1234#, X"0000DEAD" & X"00000001", IbCmd);
--    SendLocalRead(X"00010000", X"08000000", 8, 16#1234#, IbCmd);

--    SendLocalRead(X"00011000", X"08000000", 8, 16#1234#, IbCmd);
   SendLocalWrite(X"00011000", X"08000000", 8, 16#1234#, X"0000000D" & X"00000000", IbCmd);
--    SendLocalRead(X"00011000", X"08000000", 8, 16#1234#, IbCmd);

--    ib_op(ib_local_read(X"00010000", X"08000000", 8, 16#1234#, false));
--    ib_op(ib_local_write(X"00010000", X"08000000", 8, 16#1234#, '0', X"0000DEAD" & X"BEEF1234"));
--    ib_op(ib_local_read(X"00010000", X"08000000", 8, 16#1234#, false));
-- 
--    ib_op(ib_local_read(X"00011000", X"08000000", 8, 16#1234#, false));
--    ib_op(ib_local_write(X"00011000", X"08000000", 8, 16#1234#, '0', X"00000000" & X"00000000"));
--    ib_op(ib_local_read(X"00011000", X"08000000", 8, 16#1234#, false));
-- 
--    wait for 3*CLKPER;
-- 
--    ib_op(ib_read_completition(X"00010000", X"08000000", 24, 16#0400#, "desc_data.txt"));

   wait;

end process;


end architecture behavioral;
-- ----------------------------------------------------------------------------

