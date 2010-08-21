--
-- testbench.vhd: Testbench for CB2BM
-- Copyright (C) 2003 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant clkper            : time := 10 ns;
   constant reset_time        : time := 10 * clkper;
   
   -- ------------------ Components declaration -------------------------------
   component CB2BM_CORE is
      port(
         CLK            : in  std_logic;
         RESET          : in  std_logic;
         
         -- Control Bus Endpoint interface
         UPS_DATA       : out std_logic_vector(15 downto 0);
         UPS_SOP        : out std_logic;
         UPS_EOP        : out std_logic;
         UPS_SRC_RDY    : out std_logic;
         UPS_DST_RDY    : in  std_logic;
         DNS_DATA       : in  std_logic_vector(15 downto 0);
         DNS_SOP        : in  std_logic;
         DNS_EOP        : in  std_logic;
         DNS_SRC_RDY    : in  std_logic;
         DNS_DST_RDY    : out std_logic;
         
         -- Bus Master Controller interface
         GLOBAL_ADDR    : out std_logic_vector(63 downto 0);   -- Global Address
         LOCAL_ADDR     : out std_logic_vector(31 downto 0);   -- Local Address
         LENGTH         : out std_logic_vector(11 downto 0);   -- Length
         TAG            : out std_logic_vector(15 downto 0);   -- Operation TAG
         DIR            : out std_logic;                       -- Direction
         REQ            : out std_logic;                       -- Request
         ACK            : in  std_logic;                       -- Ack
         OP_TAG         : in  std_logic_vector(15 downto 0);   -- Operation TAG
         OP_DONE        : in  std_logic                        -- Acknowledge
      );
   end component CB2BM_CORE;

   -- ------------------ Signals declaration ----------------------------------
   signal clk           : std_logic;
   signal reset         : std_logic;
   -- Control Bus Endpoint interface
   signal ups_data      : std_logic_vector(15 downto 0);
   signal ups_sop       : std_logic;
   signal ups_eop       : std_logic;
   signal ups_src_rdy   : std_logic;
   signal ups_dst_rdy   : std_logic;
   signal dns_data      : std_logic_vector(15 downto 0);
   signal dns_sop       : std_logic;
   signal dns_eop       : std_logic;
   signal dns_src_rdy   : std_logic;
   signal dns_dst_rdy   : std_logic;
      
   -- Bus Master Controller interface
   signal global_addr   : std_logic_vector(63 downto 0);
   signal local_addr    : std_logic_vector(31 downto 0);
   signal length        : std_logic_vector(11 downto 0);
   signal tag           : std_logic_vector(15 downto 0);
   signal dir           : std_logic;
   signal req           : std_logic;
   signal ack           : std_logic;
   signal op_tag        : std_logic_vector(15 downto 0);
   signal op_done       : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin


   uut : CB2BM_CORE
      port map(
         CLK            => clk,
         RESET          => reset,
         -- Control Bus Endpoint interface
         UPS_DATA       => ups_data,
         UPS_SOP        => ups_sop,
         UPS_EOP        => ups_eop,
         UPS_SRC_RDY    => ups_src_rdy,
         UPS_DST_RDY    => ups_dst_rdy,
         DNS_DATA       => dns_data,
         DNS_SOP        => dns_sop,
         DNS_EOP        => dns_eop,
         DNS_SRC_RDY    => dns_src_rdy,
         DNS_DST_RDY    => dns_dst_rdy,
         -- Bus Master Controller interface
         GLOBAL_ADDR    => global_addr,
         LOCAL_ADDR     => local_addr,
         LENGTH         => length,
         TAG            => tag,
         DIR            => dir,
         REQ            => req,
         ACK            => ack,
         OP_TAG         => op_tag,
         OP_DONE        => op_done
      );


   -- clock generator ---------------------------------------------------------
   clk_gen : process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   -- Reset generation --------------------------------------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process
   
   -- generation of imaginary packet with selected characteristics
   procedure cb_write_bm_req(
      p_tag       : in std_logic_vector(11 downto 0);
      p_type      : in std_logic_vector(3 downto 0);
      p_length    : in std_logic_vector(11 downto 0);
      p_loc_addr  : in std_logic_vector(31 downto 0);
      p_glob_addr : in std_logic_vector(63 downto 0)
   ) is
      variable data : std_logic_vector(15 downto 0);
   begin
      data(11 downto 0) := p_tag;
      data(15 downto 12) := p_type;
      
      dns_data    <= data;
      dns_sop     <= '1';
      dns_src_rdy <= '1';
            
      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      data(11 downto 0) := p_length;
      data(15 downto 12) := (others => '0');
      
      dns_data    <= data;
      dns_sop     <= '0';

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_loc_addr(15 downto 0);

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_loc_addr(31 downto 16);

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_glob_addr(15 downto 0);

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_glob_addr(31 downto 16);

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_glob_addr(47 downto 32);

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= p_glob_addr(63 downto 48);
      dns_eop     <= '1';

      wait until CLK'event and CLK = '1';
      -- ------------------------------------------

      dns_data    <= (others => '0');
      dns_eop     <= '0';
      dns_src_rdy <= '0';
      
      wait until CLK'event and CLK = '1';

   end cb_write_bm_req;
   
   -- request has been completed
   procedure cb_write_req_done(
      p_tag       : in std_logic_vector(15 downto 0)
   ) is
   begin
      OP_TAG      <= p_tag;
      OP_DONE     <= '1';
      wait for clkper;
      OP_TAG      <= (others => '0');
      OP_DONE     <= '0';
      wait for clkper;
   end cb_write_req_done;


begin
   UPS_DST_RDY    <= '0';
   DNS_DATA       <= (others => '0');
   DNS_SOP        <= '0';
   DNS_EOP        <= '0';
   DNS_SRC_RDY    <= '0';
   ACK            <= '0';
   OP_TAG         <= (others => '0');
   OP_DONE        <= '0';

   wait for reset_time;
   wait until CLK'event and CLK = '1';

   -- generate BM requests
   -- params: tag, type, length, local address, global address
   cb_write_bm_req(X"123", X"2", X"500", X"80706050", X"FEDCBA9876543210");
   
   -- Acknowledge received request
   wait for clkper;
   ACK        <= '1';
   wait for clkper;

   -- send Operation Done message
   cb_write_req_done(X"2123");
   wait for 3*clkper;
   UPS_DST_RDY <= '1';
   wait for clkper;

   -- try to send 16 request without OP_DONE -> DNS_DST_RDY should fall down
   -- before the last request
   wait until CLK'event and CLK = '1';
   for i in 0 to 15 loop
      cb_write_bm_req(conv_std_logic_vector(i,12), X"2", X"500", X"80706050", X"FEDCBA9876543210");
   end loop;
   
   -- free all 15 requests
   for i in 0 to 14 loop
      cb_write_req_done(X"2" & conv_std_logic_vector(i,12));
   end loop;
   wait;
end process;

end architecture behavioral;
