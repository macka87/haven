-- rx_dma_ctrl_tb_cosim.vhd: Testbench File
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cosim_rx_dma_ctrl is
   port (
    -- Common interface
      CLK         : in std_logic;
      RESET       : out std_logic;
      INTERRUPT   : in std_logic;

      -- Receive buffer interface
      HW_PTR      : out std_logic_vector(15 downto 0);
      HW_LEN      : in std_logic_vector(15 downto 0);
      HW_LEN_EN   : in std_logic;

      -- Memory interface
      -- Write interface
      WR_ADDR     : out std_logic_vector(31 downto 0);
      WR_DATA     : out std_logic_vector(63 downto 0);
      WR_BE       : out std_logic_vector(7 downto 0);
      WR_REQ      : out std_logic;
      WR_RDY      : in std_logic;
      -- Read interface
      RD_ADDR     : out std_logic_vector(31 downto 0);
      RD_BE       : out std_logic_vector(7 downto 0);
      RD_REQ      : out std_logic;
      RD_DATA     : in std_logic_vector(63 downto 0);
      RD_SRC_RDY  : in std_logic;
      RD_DST_RDY  : out std_logic;

      -- Busmaster interface
      -- Input
      BM_GLOBAL_ADDR : in std_logic_vector(63 downto 0);  -- Global address
      BM_LOCAL_ADDR  : in std_logic_vector(31 downto 0);  -- Local address
      BM_LENGTH      : in std_logic_vector(11 downto 0);  -- Length
      BM_TAG         : in std_logic_vector(15 downto 0);  -- Operation tag
      BM_TRANS_TYPE  : in std_logic_vector(1 downto 0);   -- Transaction type
      BM_REQ         : in std_logic;                      -- Request
      BM_ACK         : out std_logic;                       -- Ack
      -- Output
      BM_OP_TAG      : out std_logic_vector(15 downto 0);   -- Operation tag
      BM_OP_DONE     : out std_logic                       -- Acknowledge
   );
end entity cosim_rx_dma_ctrl;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of cosim_rx_dma_ctrl is

   -- Constant declaration

   constant TEST_BASE_ADDR       : integer := 16#0#;
   constant TEST_LIMIT           : std_logic_vector(31 downto 0) := X"00200000";

   signal tb_reset            : std_logic;
   -- Switch1 Map
   signal internal_bus        : t_internal_bus64;
   signal switch1_port1       : t_internal_bus64;
   signal switch1_port2       : t_internal_bus64;

   -- endpoint Map
   signal ib_wr               : t_ibmi_write64;
   signal ib_rd               : t_ibmi_read64s;
  
   -- IB_SIM component ctrl      
   signal ib_sim_ctrl         : t_ib_ctrl;
   signal ib_sim_strobe       : std_logic;
   signal ib_sim_busy         : std_logic;

   signal ib_clk               : std_logic; 

begin

RESET <= tb_reset;
ib_clk <= CLK;
WR_ADDR <= ib_wr.addr;
WR_DATA <= ib_wr.data;
WR_BE   <= ib_wr.be;
WR_REQ  <= ib_wr.req;
ib_wr.rdy <= WR_RDY;

RD_ADDR <= ib_rd.addr;
RD_BE   <= ib_rd.be;
RD_REQ  <= ib_rd.req;
ib_rd.data <= RD_DATA;
ib_rd.src_rdy <= RD_SRC_RDY;
RD_DST_RDY <= ib_rd.dst_rdy;

-- ------------------------------------------------------------------
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
      IB_RESET       => tb_reset,
      -- Upstream Port
      PORT0          => internal_bus,
      -- Downstream Ports
      PORT1          => switch1_port1,
      PORT2          => switch1_port2
   );
   
-- Internal Bus Endpoint ---------------------------------------------------
IB_ENDPOINT_I : entity work.IB_ENDPOINT
   generic map(
--       BASE_ADDR     => conv_std_logic_vector(TEST_BASE_ADDR, 32),
      LIMIT         => TEST_LIMIT
   )
   port map(
      -- Common Interface
      IB_CLK        => ib_clk,
      IB_RESET      => tb_reset,
      -- Internal Bus Interface
      INTERNAL_BUS  => switch1_port1,
      -- User Component Interface
      WR            => ib_wr,
      RD            => ib_rd
   );

-- Internal Bus simulation component ---------------------------------------
IB_SIM_I : entity work.IB_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt"
   )
   port map (
      -- Common interface
      IB_RESET           => tb_reset,
      IB_CLK             => ib_clk,

      -- Internal Bus Interface
      INTERNAL_BUS       => internal_bus,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl,
      STROBE             => ib_sim_strobe,
      BUSY               => ib_sim_busy
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
   tb_reset <= '1', '0' after 100 ns;

   wait for 300 ns;

   ib_op(ib_local_read(X"00011000", X"00080000", 8, 16#1234#));

   wait;
end process;


end architecture behavioral;
-- ----------------------------------------------------------------------------

