--
-- sw_rxbuf_tb.vhd: Testbench for SW_RXBUF
-- Copyright (C) 2006 CESNET
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
use work.math_pack.all;
use work.sw_rxbuf_addr_pkg.all;
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

   constant clkper_50            : time    := 20 ns;
   constant clkper_100           : time    := 10 ns;
   constant reset_time           : time    := 10 * clkper_100;
   
   constant TEST_BASE_ADDR       : integer := 16#0#;
   
   constant TEST_DATA_WIDTH      : integer := 64;
   constant TEST_LIMIT           : std_logic_vector(31 downto 0) := X"00200000";
   constant TEST_BMEM_ITEMS      : integer := 64;
   constant TEST_BMEM_MAX_BLOCKS : integer := 32;
   constant TEST_CTRL_MEM_ITEMS  : integer := 16;
   constant TEST_CONTROL_SIZE    : integer := 32;
   constant TEST_HEADER          : boolean := true;
   constant TEST_FOOTER          : boolean := true;
   constant TEST_RX_COUNT        : integer := 1;

   -- -----------------------Testbench auxilarity signals----------------------
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

   -- SW_RXBUF signals
   -- input FrameLink interface
   signal rx_sof_n            : std_logic;
   signal rx_sop_n            : std_logic;
   signal rx_eop_n            : std_logic;
   signal rx_eof_n            : std_logic;
   signal rx_src_rdy_n        : std_logic;
   signal rx_dst_rdy_n        : std_logic;
   signal rx_data             : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal rx_rem              : std_logic_vector(log2(TEST_DATA_WIDTH/8)-1 
                                                                     downto 0);
   -- control bus interface
   signal ctrl_offset         : std_logic_vector(19 downto 0);
   signal ctrl_length         : std_logic_vector(11 downto 0);
   signal ctrl_ifc            : std_logic_vector(3 downto 0);
   signal info_ready          : std_logic;
   signal ack                 : std_logic;
   signal free_packet         : std_logic;
   
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
   -- SW_RXBUF signals
   signal cb_ctrl_offset      : std_logic_vector(TEST_RX_COUNT*20-1 downto 0);
   signal cb_ctrl_length      : std_logic_vector(TEST_RX_COUNT*12-1 downto 0);
   signal cb_info_ready       : std_logic_vector(TEST_RX_COUNT-1 downto 0);
   signal cb_ack              : std_logic_vector(TEST_RX_COUNT-1 downto 0);
   signal cb_free_packet      : std_logic_vector(TEST_RX_COUNT-1 downto 0);
   
   -- CLK setting
   alias ib_clk               : std_logic is clk100;
   alias clk                  : std_logic is clk100;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.SW_RXBUF
      generic map(
         DATA_WIDTH     => TEST_DATA_WIDTH,
         BMEM_ITEMS     => TEST_BMEM_ITEMS,
         BMEM_MAX_BLOCKS=> TEST_BMEM_MAX_BLOCKS,
         CTRL_MEM_ITEMS => TEST_CTRL_MEM_ITEMS,
         CONTROL_SIZE   => TEST_CONTROL_SIZE,
         HEADER         => TEST_HEADER,
         FOOTER         => TEST_FOOTER
      )
      port map(
         CLK            => clk100,
         RESET          => reset,
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
         RD_DST_RDY     => ib_rd.dst_rdy,
         -- input FrameLink interface
         RX_SOF_N       => rx_sof_n,
         RX_SOP_N       => rx_sop_n,
         RX_EOP_N       => rx_eop_n,
         RX_EOF_N       => rx_eof_n,
         RX_SRC_RDY_N   => rx_src_rdy_n,
         RX_DST_RDY_N   => rx_dst_rdy_n,
         RX_DATA        => rx_data,
         RX_REM         => rx_rem,
         RX_SKIP_HEADER => '0',
         -- control bus interface
         CTRL_OFFSET    => ctrl_offset,
         CTRL_LENGTH    => ctrl_length,
         CTRL_IFC       => ctrl_ifc,
         INFO_READY     => info_ready,
         ACK            => ack,
         FREE_PACKET    => free_packet
      );

   SWR_CB_MGMT_I : entity work.SWR_CB_MGMT
      generic map(
         COUNT          => TEST_RX_COUNT
      )
      port map(
         CLK            => clk100,
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
         -- SW_RXBUF Control Bus interface
         CTRL_OFFSET    => cb_ctrl_offset,
         CTRL_LENGTH    => cb_ctrl_length,
         CTRL_IFC       => ctrl_ifc,
         INFO_READY     => cb_info_ready,
         ACK            => cb_ack,
         FREE_PACKET    => cb_free_packet
      );
   
   GEN_CASE1 : if (TEST_RX_COUNT > 1) generate
      cb_ctrl_offset(19 downto 0) <= (others => '0');
      cb_ctrl_length(11 downto 0) <= (others => '0');
      cb_info_ready(0) <= '0';
      
      cb_ctrl_offset(39 downto 20) <= ctrl_offset;
      cb_ctrl_length(23 downto 12) <= ctrl_length;
      cb_info_ready(1) <= info_ready;
      ack         <= cb_ack(1);
      free_packet <= cb_free_packet(1);
   end generate;

   GEN_CASE2 : if (TEST_RX_COUNT = 1) generate
      cb_ctrl_offset    <= ctrl_offset;
      cb_ctrl_length    <= ctrl_length;
      cb_info_ready(0)  <= info_ready;
      ack               <= cb_ack(0);
      free_packet       <= cb_free_packet(0);
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
   
   procedure free_packet(ifc : in integer) is
   begin
      
      dns_data    <= X"0" & conv_std_logic_vector(ifc, 4) & X"00";
      dns_sop     <= '1';
      dns_eop     <= '1';
      dns_src_rdy <= '1';
      wait for clkper_100;
      dns_data    <= X"0000";
      dns_sop     <= '0';
      dns_eop     <= '0';
      dns_src_rdy <= '0';      
      
   end free_packet;

   -- Support for ib_op
   procedure ib_op(ctrl : in t_ib_ctrl) is
   begin
      wait until (IB_CLK'event and IB_CLK='1' and ib_sim_busy = '0');
      ib_sim_ctrl <= ctrl;
      ib_sim_strobe <= '1';
      wait until (IB_CLK'event and IB_CLK='1');
      ib_sim_strobe <= '0';
   end ib_op;

   -- generation of imaginary packet with selected characteristics
   procedure generate_packet(
      p_offset       : in integer;  -- where the counter should start
      p_hdr_length   : in integer;
      p_pld_length   : in integer;
      p_ftr_length   : in integer
   ) is
   begin

      rx_src_rdy_n<= '0';
      
      -- generate header
      for i in p_offset to p_offset+p_hdr_length-1 loop
         rx_sof_n    <= '1';
         rx_sop_n    <= '1';
         rx_eop_n    <= '1';
         rx_eof_n    <= '1';
         rx_rem      <= (others => '0');
      
         if (i = p_offset) then
            rx_sof_n <= '0';
            rx_sop_n <= '0';
         end if;
   
         if (i = p_offset+p_hdr_length-1) then
            rx_eop_n <= '0';
            rx_rem   <= conv_std_logic_vector(1, log2(TEST_DATA_WIDTH/8));
         end if;
         
         rx_data     <= conv_std_logic_vector(i, TEST_DATA_WIDTH);
         
         wait for clkper_100;
      end loop;
   
      -- generate payload
      for i in p_offset+p_hdr_length to 
               p_offset+p_hdr_length+p_pld_length-1 loop
         rx_sof_n    <= '1';
         rx_sop_n    <= '1';
         rx_eop_n    <= '1';
         rx_eof_n    <= '1';
         rx_rem      <= (others => '0');

         if rx_dst_rdy_n = '1' then
            free_packet(0);
            wait for clkper_100;
         end if;
      
         if (i = p_offset+p_hdr_length) then
            rx_sop_n <= '0';
         end if;
   
         if (i = p_offset+p_hdr_length+p_pld_length-1) then
            rx_eop_n <= '0';
            
            if p_ftr_length = 0 then
               rx_eof_n <= '0';
            end if;

            rx_rem   <= conv_std_logic_vector(2, log2(TEST_DATA_WIDTH/8));
         end if;
         
         rx_data     <= conv_std_logic_vector(i, TEST_DATA_WIDTH);
         
         wait for clkper_100;
         wait until (clk100'event and clk100='1');
      end loop;

      -- generate footer
      for i in p_offset+p_hdr_length+p_pld_length to
               p_offset+p_hdr_length+p_pld_length+p_ftr_length-1 loop
         rx_sof_n    <= '1';
         rx_sop_n    <= '1';
         rx_eop_n    <= '1';
         rx_eof_n    <= '1';
         rx_rem      <= (others => '0');
      
         if (i = p_offset+p_hdr_length+p_pld_length) then
            rx_sop_n <= '0';
         end if;
   
         if (i = p_offset+p_hdr_length+p_pld_length+p_ftr_length-1) then
            rx_eop_n <= '0';
            rx_eof_n <= '0';
            rx_rem   <= conv_std_logic_vector(3, log2(TEST_DATA_WIDTH/8));
         end if;
         
         rx_data     <= conv_std_logic_vector(i, TEST_DATA_WIDTH);
         
         wait for clkper_100;
      end loop;

      rx_sof_n    <= '1';
      rx_sop_n    <= '1';
      rx_eop_n    <= '1';
      rx_eof_n    <= '1';
      rx_rem      <= (others => '0');
      rx_src_rdy_n<= '1';
      
      wait for clkper_100;

   end generate_packet;

begin

   -- Swich 1 mapping
   switch1_port2.UP.src_rdy_n    <= '1';  -- Data Is Not Ready
   switch1_port2.UP.eop_n        <= '1';  -- Not EOP
   switch1_port2.UP.sop_n        <= '1';  -- Not SOP
   switch1_port2.UP.data         <= X"0000000000000000"; -- DATA
   switch1_port2.DOWN.dst_rdy_n  <= '0'; -- Dst Rdy

   rx_sof_n    <= '1';
   rx_sop_n    <= '1';
   rx_eop_n    <= '1';
   rx_eof_n    <= '1';
   rx_data     <= (others => '0');
   rx_rem      <= (others => '0');
   rx_src_rdy_n<= '1';

   dns_data    <= (others => '0');
   dns_sop     <= '0';
   dns_eop     <= '0';
   dns_src_rdy <= '0';

   ups_dst_rdy <= '1';

   wait for reset_time;
   
   wait until (clk100'event and clk100='1');
   generate_packet(1, 1, 14, 2);
   wait for 2*clkper_100;
   free_packet(1);
   wait for clkper_100;
   generate_packet(256, 1, 20, 2);
   wait for clkper_100;
   generate_packet(256, 1, 20, 2);
   
   -- try to read first packet from memory
   ib_op(ib_local_read(SW_RXBUF_BMEM, X"00080000",80, 16#1234#));

   wait;
end process;

end architecture behavioral;
