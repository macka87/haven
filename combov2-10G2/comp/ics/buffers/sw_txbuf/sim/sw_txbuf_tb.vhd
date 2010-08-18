--
-- sw_txbuf_tb.vhd: Testbench for SW_TXBUF
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek    <kosek@liberouter.org>
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
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.sw_txbuf_addr_pkg.all;
use work.addr_space.all;
use work.ib_pkg.all; -- Internal Bus Package
use work.ib_sim_oper.all; -- Internal Bus Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant clkper_50         : time    := 20 ns;
   constant clkper_100        : time    := 10 ns;
   constant reset_time        : time    := 20 * clkper_100;
   
   constant TEST_DATA_WIDTH   : integer := 64;
   constant TEST_OUTPUT_WIDTH : integer := 16;
   constant TEST_LIMIT        : std_logic_vector := X"00200000";
   constant TEST_BMEM_ITEMS   : integer := 32;
   constant TEST_CTRL_MEM_ITEMS        : integer := 16;
   constant TEST_CONTROL_DATA_LENGTH   : integer := 0;
   constant TEST_TX_COUNT     : integer := 1;
   -- send constant HW header for every outcomming packet
   constant TEST_CONSTANT_HW_HEADER_LENGTH : integer := 4;
   -- constant HW header data in Bytes (maximaly 8 Bytes)
   constant TEST_CONSTANT_HW_HEADER_DATA   : std_logic_vector(63 downto 0) 
                                       := X"FEDCBA9876543210";
   
   -- ----------------------- Testbench auxilary signals ----------------------
   -- CLK_GEN Signals
   signal reset               : std_logic;
   signal clk50               : std_logic;
   signal clk100              : std_logic;
   signal lock                : std_logic;

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
   signal drd_cnt             : std_logic_vector(63 downto 0);
   signal drd_cnt_ce          : std_logic;
   signal drd_cnt_ld          : std_logic;
   signal rdy_write_pipe      : std_logic;      
   signal counter             : std_logic_vector(2 downto 0);
   signal drdy_rd_pipe        : std_logic_vector(9 downto 0);

   -- SW_TXBUF signals
   -- output interface
   signal sof_n               : std_logic;
   signal sop_n               : std_logic;
   signal eop_n               : std_logic;
   signal eof_n               : std_logic;
   signal src_rdy_n           : std_logic;
   signal dst_rdy_n           : std_logic;
   signal data_out            : std_logic_vector(TEST_OUTPUT_WIDTH-1 downto 0);
   signal rem_out             : std_logic_vector(log2(TEST_OUTPUT_WIDTH/8)-1 
                                                                     downto 0);
   -- control bus interface
   signal diff                : std_logic_vector(log2(TEST_CTRL_MEM_ITEMS) 
                                                                     downto 0);
   signal ready               : std_logic;
   signal ack                 : std_logic;
   signal ctrl_offset         : std_logic_vector(19 downto 0);
   signal ctrl_length         : std_logic_vector(11 downto 0);
   signal ctrl_ready          : std_logic;
   signal ctrl_write          : std_logic;

   -- Control Bus Management Unit signals
   -- User Component Upstream Interface
   signal ups_data            : std_logic_vector(15 downto 0);
   signal ups_sop             : std_logic;
   signal ups_eop             : std_logic;
   signal ups_src_rdy         : std_logic;
   signal ups_dst_rdy         : std_logic;
   -- User Component Downstream Interface
   signal dns_data            : std_logic_vector(15 downto 0);
   signal dns_sop             : std_logic;
   signal dns_eop             : std_logic;
   signal dns_src_rdy         : std_logic;
   signal dns_dst_rdy         : std_logic;
   -- SW_TXBUF signals
   signal cb_diff             : std_logic_vector(TEST_TX_COUNT
                                *(log2(TEST_CTRL_MEM_ITEMS)+1)-1 downto 0);
   signal cb_ready            : std_logic_vector(TEST_TX_COUNT-1 downto 0);
   signal cb_ack              : std_logic_vector(TEST_TX_COUNT-1 downto 0);
   signal cb_ctrl_offset      : std_logic_vector(19 downto 0);
   signal cb_ctrl_length      : std_logic_vector(11 downto 0);
   signal cb_ctrl_ready       : std_logic_vector(TEST_TX_COUNT-1 downto 0);
   signal cb_ctrl_write       : std_logic_vector(TEST_TX_COUNT-1 downto 0);
   
   -- others
   signal rd_dst_rdy          : std_logic;

   -- CLK setting
   alias ib_clk               : std_logic is clk100;
   alias clk                  : std_logic is clk100;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.SW_TXBUF
      generic map(
         DATA_WIDTH     => TEST_DATA_WIDTH,
         OUTPUT_WIDTH   => TEST_OUTPUT_WIDTH,
         BMEM_ITEMS     => TEST_BMEM_ITEMS,
         CTRL_MEM_ITEMS => TEST_CTRL_MEM_ITEMS,
         CONTROL_DATA_LENGTH => TEST_CONTROL_DATA_LENGTH,
         -- send constant HW header for every outcomming packet
         CONSTANT_HW_HEADER_LENGTH => TEST_CONSTANT_HW_HEADER_LENGTH,
         -- constant HW header data in Bytes (maximaly 8 Bytes)
         CONSTANT_HW_HEADER_DATA => TEST_CONSTANT_HW_HEADER_DATA
      )
      port map(
         CLK            => clk,
         RESET          => reset,
         -- output interface
         SOF_N          => sof_n,
         SOP_N          => sop_n,
         EOP_N          => eop_n,
         EOF_N          => eof_n,
         SRC_RDY_N      => src_rdy_n,
         DST_RDY_N      => dst_rdy_n,
         DATA_OUT       => data_out,
         REM_OUT        => rem_out,
         -- Internal Bus: Write Interface
         WR_ADDR        => ib_wr.addr,
         WR_DATA        => ib_wr.data,
         WR_BE          => ib_wr.be,
         WR_REQ         => ib_wr.req,
         WR_RDY         => ib_wr.rdy,
         WR_LENGTH      => ib_wr.length,
         WR_SOF         => ib_wr.sof,
         WR_EOF         => ib_wr.eof,
         -- Internal Bus: Read Interface
         -- Input Interface
         RD_ADDR        => ib_rd.addr,
         RD_BE          => ib_rd.be,
         RD_REQ         => ib_rd.req,
         RD_ARDY        => ib_rd.ardy,
         RD_SOF_IN      => ib_rd.sof_in,
         RD_EOF_IN      => ib_rd.eof_in,
         -- Output Interface
         RD_DATA        => ib_rd.data,
         RD_SRC_RDY     => ib_rd.src_rdy,
         RD_DST_RDY     => rd_dst_rdy,
         -- control bus interface
         DIFF           => diff,
         READY          => ready,
         ACK            => ack,
         CTRL_OFFSET    => ctrl_offset,
         CTRL_LENGTH    => ctrl_length,
         CTRL_READY     => ctrl_ready,
         CTRL_WRITE     => ctrl_write
      );

   SWT_CB_MGMT_I : entity work.SWT_CB_MGMT
      generic map(
         COUNT          => TEST_TX_COUNT,
         CTRL_MEM_ITEMS => TEST_CTRL_MEM_ITEMS
      )
      port map(
         CLK            => clk,
         RESET          => reset,
         -- Control Bus interface
         -- User Component Upstream Interface
         UPS_DATA       => ups_data,
         UPS_SOP        => ups_sop,
         UPS_EOP        => ups_eop,
         UPS_SRC_RDY    => ups_src_rdy,
         UPS_DST_RDY    => ups_dst_rdy,
         -- User Component Downstream Interface
         DNS_DATA       => dns_data,
         DNS_SOP        => dns_sop,
         DNS_EOP        => dns_eop,
         DNS_SRC_RDY    => dns_src_rdy,
         DNS_DST_RDY    => dns_dst_rdy,
         -- SW_TXBUF Control Bus interface
         DIFF           => cb_diff,
         READY          => cb_ready,
         ACK            => cb_ack,
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_READY     => cb_ctrl_ready,
         CTRL_WRITE     => cb_ctrl_write
      );

   GEN_CASE1 : if (TEST_TX_COUNT > 1) generate
      cb_diff(2*(log2(TEST_CTRL_MEM_ITEMS)+1)-1 
              downto (log2(TEST_CTRL_MEM_ITEMS)+1)) <= diff;
      cb_ready(1) <= ready;
      ack         <= cb_ack(1);
      ctrl_offset <= cb_ctrl_offset;
      ctrl_length <= cb_ctrl_length;
      cb_ctrl_ready(1)  <= ctrl_ready;
      ctrl_write  <= cb_ctrl_write(1);
      
      
      cb_diff(log2(TEST_CTRL_MEM_ITEMS) downto 0) <= (others => '0');
      cb_ctrl_ready(0)  <= '0';
      cb_ready(0)       <= '0';

   end generate;

   GEN_CASE2 : if (TEST_TX_COUNT = 1) generate
      cb_diff     <= diff;
      cb_ready(0) <= ready;
      ack         <= cb_ack(0);
      ctrl_offset <= cb_ctrl_offset;
      ctrl_length <= cb_ctrl_length;
      cb_ctrl_ready(0) <= ctrl_ready;
      ctrl_write  <= cb_ctrl_write(0);
   end generate;

   -- Reset generation --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;
   
   -- clk50 generator ---------------------------------------------------------
   clk50_gen : process
   begin
      clk50 <= '1';
      wait for clkper_50/2;
      clk50 <= '0';
      wait for clkper_50/2;
   end process;
   
   -- clk100 generator --------------------------------------------------------
   clk100_gen : process
   begin
      clk100 <= '1';
      wait for clkper_100/2;
      clk100 <= '0';
      wait for clkper_100/2;
   end process;

   
   -- Internal Bus Switch -----------------------------------------------------
   IB_SWITCH1_I : entity work.IB_SWITCH
      generic map (
         -- Data Width (64/128)
         DATA_WIDTH        => 64,
         -- Port 0 Address Space
         SWITCH_BASE        => X"00000000",
         SWITCH_LIMIT       => X"01000000",
         -- Port 1 Address Space
         DOWNSTREAM0_BASE   => SW_TXBUF_BASE_ADDR,
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

   IB_ENDPOINT_I : entity work.IB_ENDPOINT
      generic map(
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
         IB_RESET           => reset,
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

   procedure swt_cb_write_ctrl(
      p_ifc       : in integer;
      p_offset    : in integer;
      p_length    : in integer
   ) is
      variable data : std_logic_vector(15 downto 0);
      variable offset : std_logic_vector(19 downto 0);
   begin
      
      
      offset      := conv_std_logic_vector(p_offset,20);
      
      data(11 downto 0)  := conv_std_logic_vector(p_length,12);
      data(15 downto 12) := (others => '0');
      
      dns_data    <= data;
      dns_sop     <= '1';
      dns_src_rdy <= '1';
            
      wait until clk'event and clk = '1';
      --wait for clkper_100;

      data(3 downto 0)   := offset(19 downto 16);
      data(11 downto 4)  := (others => '0');
      data(15 downto 12) := conv_std_logic_vector(p_ifc,4);
      
      dns_data    <= data;
      dns_sop     <= '0';
            
      wait until clk'event and clk = '1';

      data(15 downto 0)  := offset(15 downto 0);
      
      dns_data    <= data;
      dns_eop     <= '1';
            
      wait until clk'event and clk = '1';
      
      dns_data    <= (others => '0');
      dns_eop     <= '0';
      dns_src_rdy <= '0';
      
      wait until clk'event and clk = '1';

   end swt_cb_write_ctrl;

   procedure swt_ib_write_ctrl(
      p_offset    : in integer;
      p_length    : in integer
   ) is
      variable data : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   begin
      data(TEST_DATA_WIDTH-1 downto 0) := (others => '0');
      data(19 downto 0) := conv_std_logic_vector(p_offset, 20);
      data(31 downto 20) := conv_std_logic_vector(p_length, 12);
      
      ib_op(ib_local_write(SW_TXBUF_FIFO, X"00C00000", 4, 16#1234#, '0' ,data));
            
   end swt_ib_write_ctrl;

   procedure swt_enable_ack is
      variable data : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   begin
      data(TEST_DATA_WIDTH-1 downto 1) := (others => '0');
      data(0) := '1';
      
      ib_op(ib_local_write(SW_TXBUF_ACK, X"00C00000", 1, 16#1234#, '0', data));
   end swt_enable_ack;

begin

   -- Swich 1 mapping
   switch1_port2.UP.src_rdy_n    <= '1';  -- Data Is Not Ready
   switch1_port2.UP.eop_n        <= '1';  -- Not EOP
   switch1_port2.UP.sop_n        <= '1';  -- Not SOP
   switch1_port2.UP.data         <= X"0000000000000000"; -- DATA
   switch1_port2.DOWN.dst_rdy_n  <= '0'; -- Dst Rdy

   dst_rdy_n <= '1';
   
   dns_data    <= (others => '0');
   dns_sop     <= '0';
   dns_eop     <= '0';
   dns_src_rdy <= '0';

   ups_dst_rdy <= '1';
   rd_dst_rdy  <= '1';

   wait for reset_time;
   
   swt_enable_ack;

   -- write data into BMEM
   --for i in 0 to 31 loop
   --   ib_op(ib_local_write(SW_TXBUF_BMEM+conv_std_logic_vector(i*8,32), 
   --         X"00C00000", 8, 16#1234#, '0', conv_std_logic_vector(i, TEST_DATA_WIDTH)));
   --end loop;
   ib_op(ib_local_write_file(SW_TXBUF_BMEM, X"ffffffff", 0, 1, '0', "memory.bin"));
   
   -- Write records into Control memory via Internal Bus
   --swt_ib_write_ctrl(1, 60);
   --swt_ib_write_ctrl(4, 32);
   
   -- Write records into Control memory via Control Bus
   swt_cb_write_ctrl(1, 16#0#, 10);
   swt_cb_write_ctrl(1, 16#0#, 11);
   swt_cb_write_ctrl(1, 16#0#, 12);
   swt_cb_write_ctrl(1, 16#0#, 13);
   swt_cb_write_ctrl(1, 16#0#, 14);
   swt_cb_write_ctrl(1, 16#0#, 15);
   swt_cb_write_ctrl(1, 16#0#, 16);
   swt_cb_write_ctrl(1, 16#0#, 17);
   swt_cb_write_ctrl(1, 16#0#, 18);
   swt_cb_write_ctrl(1, 16#0#, 19);
   swt_cb_write_ctrl(1, 16#0#, 20);
   swt_cb_write_ctrl(1, 16#0#, 21);
   swt_cb_write_ctrl(1, 16#0#, 22);
   --swt_cb_write_ctrl(1, 16#20#, 32);
   
   -- try to read some values
   ib_op(ib_local_read(SW_TXBUF_BMEM,X"00C00000", 80, 16#1234#));
   
   -- simulate interrupted read
   wait until ib_rd.eof_in = '1';
   rd_dst_rdy  <= '0';
   wait for 2*clkper_100;
   rd_dst_rdy  <= '1';

   ib_op(ib_local_read(SW_TXBUF_CTRL,X"00C00000", 16, 16#1234#));
   ib_op(ib_local_read(SW_TXBUF_ACK,X"00C00000", 4, 16#1234#));
   ib_op(ib_local_read(SW_TXBUF_STATUS,X"00C00000", 4, 16#1234#));
   
   dst_rdy_n   <= '0';
   
   -- simulate DST_RDY interruption
   wait for 8*clkper_100;
   wait until clk'event and clk='1';
   dst_rdy_n   <= '1';
   wait until clk'event and clk='1';
   dst_rdy_n   <= '0';
   wait until clk'event and clk='1';
   dst_rdy_n   <= '1';
   wait until clk'event and clk='1';
   dst_rdy_n   <= '0';

   wait;
end process;

end architecture behavioral;
