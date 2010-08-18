-- testbench2.vhd: Tag Sequencer testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <Pus@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RESET_TIME     : time      := 10*CLKPER + 0.1 ns;
constant TAG_WIDTH      : integer   := 3;

signal clk           : std_logic;
signal reset         : std_logic;

signal usr_tag     : std_logic_vector(TAG_WIDTH-1 downto 0);
signal ep_tag      : std_logic_vector(TAG_WIDTH-1 downto 0);
signal usr_req     : std_logic;
signal ep_req      : std_logic;
signal reg_ep_req      : std_logic;
signal usr_ack     : std_logic;
signal usr_trans_type     : std_logic_vector(1 downto 0);
signal ep_trans_type     : std_logic_vector(1 downto 0);
signal ep_ack      : std_logic;
signal ep_op_tag   : std_logic_vector(TAG_WIDTH-1 downto 0);
signal usr_op_tag  : std_logic_vector(TAG_WIDTH-1 downto 0);
signal ep_op_done  : std_logic;
signal usr_op_done : std_logic;

begin

   uut : entity work.tag_sequencer
   generic map(
      EP_TAG_WIDTH => TAG_WIDTH,
      USR_TAG_WIDTH => TAG_WIDTH
   )
   port map(
      CLK         => clk,
      RESET       => reset,
      
      USR_TAG     => usr_tag,
      USR_REQ     => usr_req,
      USR_ACK     => usr_ack,
      USR_TRANS_TYPE => usr_trans_type,
      EP_REQ      => ep_req,
      EP_TAG      => ep_tag,
      EP_ACK      => ep_ack,
      EP_TRANS_TYPE => ep_trans_type,
                                
      EP_OP_TAG   => ep_op_tag,
      USR_OP_TAG  => usr_op_tag,
      EP_OP_DONE  => ep_op_done,
      USR_OP_DONE => usr_op_done
   );

   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   reset_gen : process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process reset_gen;

   req_tb : process
   begin
      usr_req <= '0';
      usr_trans_type <= "00";
      ep_ack <= '0';
      wait for RESET_TIME;

      wait for 5*clkper;
      wait for 1 ns;

      -- User request with tag 3
      usr_tag <= conv_std_logic_vector(3, TAG_WIDTH);
      usr_req <= '1';
      wait for clkper;
      ep_ack <= '1';
      wait for clkper;
      usr_req <= '0';
      ep_ack <= '0';
      wait for 2*clkper;

      -- User request with tag 4
      usr_tag <= conv_std_logic_vector(4, TAG_WIDTH);
      usr_req <= '1';
      wait for clkper;
      ep_ack <= '1';
      wait for clkper;
      usr_req <= '0';
      ep_ack <= '0';
      wait for 2*clkper;

      -- User request with tag 5
      usr_tag <= conv_std_logic_vector(5, TAG_WIDTH);
      usr_req <= '1';
      wait for clkper;
      ep_ack <= '1';
      wait for clkper;
      usr_req <= '0';
      ep_ack <= '0';
      wait for 2*clkper;

      -- User request with tag 6
      usr_tag <= conv_std_logic_vector(6, TAG_WIDTH);
      usr_req <= '1';
      wait for clkper;
      ep_ack <= '1';
      wait for clkper;
      usr_req <= '0';
      ep_ack <= '0';
      wait for 10*clkper;

      -- Request with tag 7
      usr_tag <= conv_std_logic_vector(7, TAG_WIDTH);
      usr_req <= '1';
      ep_ack <= '1'; -- Immediately accepted by ibep
      wait for clkper;
      ep_ack <= '0';
      usr_req <= '0';
      wait for clkper;

      -- Request with tag 8
      usr_tag <= conv_std_logic_vector(8, TAG_WIDTH);
      usr_req <= '1';
      wait for 10*clkper;
      ep_ack <= '1'; -- Accepted after 10 cycles
      wait for clkper;
      usr_req <= '0';
      ep_ack <= '0';

      wait for 10*clkper;

      for i in 0 to 12 loop
         -- Request with tag i
         usr_tag <= conv_std_logic_vector(i, TAG_WIDTH);
         usr_req <= '1';
         wait for 0.1 ns;
         if ep_req = '0' then
            ep_ack <= '0';
            wait until ep_req = '1';
            wait for 0.1 ns;
            ep_ack <= '1';
         else
            wait for 0.1 ns;
            ep_ack <= '1'; -- Immediately accepted by ibep
         end if;
         wait until clk'event and clk = '1';
         wait for 0.1 ns;
         --if usr_ack = '0' then
            --wait until usr_ack = '1';
         --end if;
         
      end loop;
      usr_req <= '0';
      ep_ack <= '0';

      wait;
   end process;

   done_tb : process
   begin
      ep_op_tag <= conv_std_logic_vector(0, TAG_WIDTH);
      ep_op_done <= '0';
      wait for RESET_TIME;

      wait for 20*clkper;

      -- Return tag 2
      ep_op_tag <= conv_std_logic_vector(2, TAG_WIDTH);
      ep_op_done <= '1';
      wait for clkper;
      ep_op_done <= '0';
      wait for 2*clkper;

      -- Return tag 3
      ep_op_tag <= conv_std_logic_vector(3, TAG_WIDTH);
      ep_op_done <= '1';
      wait for clkper;
      ep_op_done <= '0';
      wait for 2*clkper;

      -- Return tags 0 and 1
      ep_op_tag <= conv_std_logic_vector(0, TAG_WIDTH);
      ep_op_done <= '1';
      wait for clkper;
      ep_op_tag <= conv_std_logic_vector(1, TAG_WIDTH);
      wait for clkper;
      ep_op_done <= '0';
      wait for 10*clkper;

      -- Return tag 4
      ep_op_tag <= conv_std_logic_vector(4, TAG_WIDTH);
      ep_op_done <= '1';
      wait for clkper;
      ep_op_done <= '0';
      wait for 2*clkper;

      -- Return tag 5
      ep_op_tag <= conv_std_logic_vector(5, TAG_WIDTH);
      ep_op_done <= '1';
      wait for clkper;
      ep_op_done <= '0';
      wait for 2*clkper;

      wait for 20*clkper;

      for i in 0 to 12 loop
         ep_op_tag <= conv_std_logic_vector(6+i, TAG_WIDTH);
         ep_op_done <= '1';
         wait for clkper;
      end loop;
      ep_op_done <= '0';


      wait;
   end process;

end architecture;
