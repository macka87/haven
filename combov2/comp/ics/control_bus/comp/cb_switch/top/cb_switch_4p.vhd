--
-- cb_switch_4p.vhd: Envelope 4 ports switch
-- Copyright (C) 2004 CESNET
-- Author(s): Patrik Beck <beck@liberouter.org>
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
library IEEE;
use IEEE.std_logic_1164.all;
use work.cb_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cb_switch_4p is
   generic(
      DATA_WIDTH  :  integer := 16
   );
   port(
      CB_CLK      :  std_logic;
      CB_RESET    :  std_logic;

      -- upstream port
      PORT0       :  inout t_control_bus;

      -- downstream
      PORT1       :  inout t_control_bus;
      PORT2       :  inout t_control_bus;
      PORT3       :  inout t_control_bus;
      PORT4       :  inout t_control_bus
         
   );
end entity cb_switch_4p;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cb_switch_4p_arch of cb_switch_4p is
   constant DS_PORTS    : integer := 4;

   signal sig_ds_in     : std_logic_vector(DS_PORTS*(DATA_WIDTH+3)-1 downto 0);
   signal sig_ds_out    : std_logic_vector(DS_PORTS*(DATA_WIDTH+3)-1 downto 0);

   signal sig_ds_in_rd  : std_logic_vector(DS_PORTS-1 downto 0);
   signal sig_ds_out_rd : std_logic_vector(DS_PORTS-1 downto 0);

begin

CB_SWITCH: entity work.cb_switch
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      DS_PORTS       => DS_PORTS
   )
   port map(
      CB_CLK      => CB_CLK,
      CB_RESET    => CB_RESET,

      PORT0       => PORT0,

      DS_IN       => sig_ds_in,
      DS_OUT      => sig_ds_out,
      
      DS_IN_RD    => sig_ds_in_rd,
      DS_OUT_RD   => sig_ds_out_rd
      
  );

   -- downstream port 1
   sig_ds_in(1*(DATA_WIDTH+3) - 1 downto 0*(DATA_WIDTH+3) + 3)    <= PORT1.UP.data;
   sig_ds_in(0*(DATA_WIDTH+3) + 0)                                <= PORT1.UP.src_rdy_n;
   sig_ds_in(0*(DATA_WIDTH+3) + 1)                                <= PORT1.UP.eop_n;
   sig_ds_in(0*(DATA_WIDTH+3) + 2)                                <= PORT1.UP.sop_n;
   PORT1.UP.dst_rdy_n                                             <= sig_ds_in_rd(0);
 
   PORT1.DOWN.data       <= sig_ds_out(1*(DATA_WIDTH+3) - 1 downto 0*(DATA_WIDTH+3) + 3);
   PORT1.DOWN.src_rdy_n  <= sig_ds_out(0*(DATA_WIDTH+3) + 0);
   PORT1.DOWN.eop_n      <= sig_ds_out(0*(DATA_WIDTH+3) + 1);
   PORT1.DOWN.sop_n      <= sig_ds_out(0*(DATA_WIDTH+3) + 2);
   sig_ds_out_rd(0)     <= PORT1.DOWN.dst_rdy_n;
      
   -- downstream port 2
   sig_ds_in(2*(DATA_WIDTH+3) - 1 downto 1*(DATA_WIDTH+3) + 3)    <= PORT2.UP.data;
   sig_ds_in(1*(DATA_WIDTH+3) + 0)                                <= PORT2.UP.src_rdy_n;
   sig_ds_in(1*(DATA_WIDTH+3) + 1)                                <= PORT2.UP.eop_n;
   sig_ds_in(1*(DATA_WIDTH+3) + 2)                                <= PORT2.UP.sop_n;
   PORT2.UP.dst_rdy_n                                             <= sig_ds_in_rd(1);
 
   PORT2.DOWN.data       <= sig_ds_out(2*(DATA_WIDTH+3) - 1 downto 1*(DATA_WIDTH+3) + 3);
   PORT2.DOWN.src_rdy_n  <= sig_ds_out(1*(DATA_WIDTH+3) + 0);
   PORT2.DOWN.eop_n      <= sig_ds_out(1*(DATA_WIDTH+3) + 1);
   PORT2.DOWN.sop_n      <= sig_ds_out(1*(DATA_WIDTH+3) + 2);
   sig_ds_out_rd(1)     <= PORT2.DOWN.dst_rdy_n;
 
   -- downstream port 3
   sig_ds_in(3*(DATA_WIDTH+3) - 1 downto 2*(DATA_WIDTH+3) + 3)    <= PORT3.UP.data;
   sig_ds_in(2*(DATA_WIDTH+3) + 0)                                <= PORT3.UP.src_rdy_n;
   sig_ds_in(2*(DATA_WIDTH+3) + 1)                                <= PORT3.UP.eop_n;
   sig_ds_in(2*(DATA_WIDTH+3) + 2)                                <= PORT3.UP.sop_n;
   PORT3.UP.dst_rdy_n                                             <= sig_ds_in_rd(2);
 
   PORT3.DOWN.data       <= sig_ds_out(3*(DATA_WIDTH+3) - 1 downto 2*(DATA_WIDTH+3) + 3);
   PORT3.DOWN.src_rdy_n  <= sig_ds_out(2*(DATA_WIDTH+3) + 0);
   PORT3.DOWN.eop_n      <= sig_ds_out(2*(DATA_WIDTH+3) + 1);
   PORT3.DOWN.sop_n      <= sig_ds_out(2*(DATA_WIDTH+3) + 2);
   sig_ds_out_rd(2)     <= PORT3.DOWN.dst_rdy_n;
 
   -- downstream port 4
   sig_ds_in(4*(DATA_WIDTH+3) - 1 downto 3*(DATA_WIDTH+3) + 3)    <= PORT4.UP.data;
   sig_ds_in(3*(DATA_WIDTH+3) + 0)                                <= PORT4.UP.src_rdy_n;
   sig_ds_in(3*(DATA_WIDTH+3) + 1)                                <= PORT4.UP.eop_n;
   sig_ds_in(3*(DATA_WIDTH+3) + 2)                                <= PORT4.UP.sop_n;
   PORT4.UP.dst_rdy_n                                             <= sig_ds_in_rd(3);
 
   PORT4.DOWN.data       <= sig_ds_out(4*(DATA_WIDTH+3) - 1 downto 3*(DATA_WIDTH+3) + 3);
   PORT4.DOWN.src_rdy_n  <= sig_ds_out(3*(DATA_WIDTH+3) + 0);
   PORT4.DOWN.eop_n      <= sig_ds_out(3*(DATA_WIDTH+3) + 1);
   PORT4.DOWN.sop_n      <= sig_ds_out(3*(DATA_WIDTH+3) + 2);
   sig_ds_out_rd(3)     <= PORT4.DOWN.dst_rdy_n;
 
end architecture cb_switch_4p_arch;

