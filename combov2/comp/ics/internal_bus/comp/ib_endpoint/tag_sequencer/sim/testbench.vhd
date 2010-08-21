-- testbench.vhd: Tag Sequencer testbench file
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
constant RESET_TIME     : time      := 10*CLKPER + 1 ns;
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
signal reg_ep_ack1      : std_logic;
signal reg_ep_ack2      : std_logic;
signal ep_ack      : std_logic;
signal ep_op_tag   : std_logic_vector(TAG_WIDTH-1 downto 0);
signal usr_op_tag  : std_logic_vector(TAG_WIDTH-1 downto 0);
signal ep_op_done  : std_logic;
signal usr_op_done : std_logic;

begin

   uut : entity work.tag_sequencer
   generic map(
      EP_TAG_WIDTH => TAG_WIDTH,
      USR_TAG_WIDTH => TAG_WIDTH,
      WR_FIFO_DEPTH => 4
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

   usr_tb : process
   begin
      wait for RESET_TIME;
      usr_req <= '0';
      usr_trans_type <= "00";
      wait for 5*clkper;

      -- User request with tag 3
      usr_tag <= conv_std_logic_vector(3, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      wait for 8*clkper;

      -- User request with tag 4
      usr_tag <= conv_std_logic_vector(4, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      -- User request with tag 5
      usr_tag <= conv_std_logic_vector(5, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      wait for 12*clkper;
      usr_tag <= conv_std_logic_vector(6, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      usr_tag <= conv_std_logic_vector(7, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      usr_tag <= conv_std_logic_vector(8, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      usr_tag <= conv_std_logic_vector(9, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      wait for 20*clkper;

      -- Write transactions
      usr_trans_type <= "01";

      usr_tag <= conv_std_logic_vector(2, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      usr_tag <= conv_std_logic_vector(3, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

      usr_tag <= conv_std_logic_vector(4, TAG_WIDTH);
      usr_req <= '1';
      wait until CLK'event and CLK = '1';
      if usr_ack = '0' then
         wait until usr_ack = '1';
         wait until CLK'event and CLK = '1';
      end if;
      wait for 1 ns;
      usr_req <= '0';

   
      wait for 30*clkper;

      -- Multiple READ transactions
      usr_trans_type <= "00";
      for i in 0 to 17 loop
         usr_tag <= conv_std_logic_vector(i, TAG_WIDTH);
         usr_req <= '1';
         wait until CLK'event and CLK = '1';
         if usr_ack = '0' then
            --wait until usr_ack = '1';
            wait until CLK'event and CLK = '1' and usr_ack = '1';
         end if;
         wait for 1 ns;
         usr_req <= '0';
      end loop;

      wait;
   end process;

   -- ep_ack_imm_tb : process
   -- begin
      ep_ack <= ep_req;
   -- end process;

   ep_ack_tb : process(CLK)
   begin
      -- Universal ACK answer from EP
      if CLK'event and CLK = '1' then
         --ep_ack <= reg_ep_ack2;
         reg_ep_ack2 <= reg_ep_ack1;
         reg_ep_ack1 <= ep_req and not (reg_ep_ack1 or reg_ep_ack2 or ep_ack);
      end if;
   end process;

   ep_done_tb : process
   begin
      ep_op_tag <= conv_std_logic_vector(0, TAG_WIDTH);
      ep_op_done <= '0';

      -- EP answer with tag 0
      wait until ep_ack = '1';
      wait for 2*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(0, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';

      -- EP answer with tag 2
      wait until ep_ack = '1';
      wait for 10*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(2, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';

      -- EP answer with tag 1
      wait for 2*clkper;
      wait for 2*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(1, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';

      -- EP answer with tag 5
      wait for 25*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(5, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';
      -- EP answer with tag 4
      wait for 2*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(4, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';
      -- EP answer with tag 6
      wait for 1*clkper;
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(6, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';
      -- EP answer with tag 3
      ep_op_done <= '1';
      ep_op_tag <= '0' & conv_std_logic_vector(3, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';

      wait for 20*clkper;

      -- EP answers for WRITE transaction
      ep_op_done <= '1';
      ep_op_tag <= '1' & conv_std_logic_vector(1, TAG_WIDTH-1);
      wait for clkper;
      ep_op_tag <= '1' & conv_std_logic_vector(2, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';
      wait for clkper;
      ep_op_done <= '1';
      ep_op_tag <= '1' & conv_std_logic_vector(3, TAG_WIDTH-1);
      wait for clkper;
      ep_op_done <= '0';

      -- Multiple EP answers
      wait for 20*clkper;
      for i in 0 to 17 loop
         ep_op_done <= '1';
         ep_op_tag <= '0' & conv_std_logic_vector(7+i, TAG_WIDTH-1);
         wait for clkper;
         ep_op_done <= '0';
         wait for 2*clkper;
      end loop;


      wait;
   end process;

end architecture;
