--
-- ib_sim.vhd: Simulation component for internal bus
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Patrik Beck <beck@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.math_pack.all;
use work.cb_pkg.all;
use work.cb_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB_SIM is
   port(
      -- Common interface
      CB_RESET          : in  std_logic;
      CB_CLK            : in  std_logic;

      -- Control Bus Interface
      PORT0             : inout t_control_bus;

      -- CB SIM interface
      CTRL              : in  t_cb_params;
      STROBE            : in  std_logic;
      BUSY              : out std_logic
      );
end entity CB_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB_SIM_ARCH of CB_SIM is

  -- Signals
  signal port0_out_data        : std_logic_vector(15 downto 0);
  signal port0_out_sop         : std_logic;
  signal port0_out_sop_aux     : std_logic;
  signal port0_out_eop_aux     : std_logic;
  signal port0_out_eop         : std_logic;
  signal port0_out_src_rdy     : std_logic;
  signal port0_out_dst_rdy     : std_logic;

  signal cb_packet_fifo_re     : std_logic;
  signal cb_packet_fifo_we     : std_logic;
  signal cb_packet_data        : std_logic_vector(15 downto 0);
  signal cb_packet_sop         : std_logic;
  signal cb_packet_eop         : std_logic;
  signal cb_packet_fifo_full   : std_logic;
  signal cb_packet_fifo_empty  : std_logic;

begin
     
-- Port 0 Always ready
PORT0.UP.dst_rdy_n <= '0';

-- register port0_pipe ------------------------------------------------------
port0_pipep: process(CB_RESET, CB_CLK)
begin
   if (CB_RESET = '1') then
      port0.DOWN.data        <= X"0000";
      port0.DOWN.sop_n       <= '1'; 
      port0.DOWN.eop_n       <= '1';
      port0.DOWN.src_rdy_n   <= '1';
   elsif (CB_CLK'event AND CB_CLK = '1') then
     if (port0.DOWN.dst_rdy_n = '0') then
       port0.DOWN.data       <= port0_out_data;
       port0.DOWN.sop_n      <= port0_out_sop_aux;
       port0.DOWN.eop_n      <= port0_out_eop_aux;
       port0.DOWN.src_rdy_n  <= port0_out_src_rdy;
     end if;  
   end if;
end process;

-- SOP on 1 when no data rdy
port0_out_sop_aux <= '1' when cb_packet_fifo_empty = '1' else port0_out_sop;
port0_out_eop_aux <= '1' when cb_packet_fifo_empty = '1' else port0_out_eop;

-- Read when dst_rdy
cb_packet_fifo_re <= not port0.DOWN.dst_rdy_n;

-- Source ready when data and dst_rdy
port0_out_src_rdy <= '0' when (cb_packet_fifo_empty = '0' and
                               port0.DOWN.dst_rdy_n = '0') else '1';
-- ----------------------------------------------------------------------------
cb_packet_fifo: entity work.fifo
   generic map (
      ITEMS => 64,
      DATA_WIDTH => 18,
      DISTMEM_TYPE => 16
   )
   port map(
      CLK       => CB_CLK,
      RESET     => CB_RESET,
      -- Write interface
      WRITE_REQ             => cb_packet_fifo_we,
      DATA_IN(15 downto 0)  => cb_packet_data,
      DATA_IN(16)           => cb_packet_sop,
      DATA_IN(17)           => cb_packet_eop,
      FULL                  => cb_packet_fifo_full,
      LSTBLK                => open,

      -- Read interface
      READ_REQ              => cb_packet_fifo_re,
      DATA_OUT(15 downto 0) => port0_out_data,
      DATA_OUT(16)          => port0_out_sop,
      DATA_OUT(17)          => port0_out_eop,
      EMPTY                 => cb_packet_fifo_empty
      ); 


main : process
-- ----------------------------------------------------------------
--                        Process Body
-- ----------------------------------------------------------------
variable ident        : std_logic_vector(3 downto 0);
variable buffer_space : std_logic_vector(7 downto 0);
variable data         : std_logic_vector(15 downto 0);

begin

-- Wait when reset
wait until (CB_RESET = '0');

-- Do main loop
while true loop
  BUSY <= '0';
  wait until (STROBE = '1');
  BUSY <= '1';

   -- Get Data for creating packet
   ident        := conv_std_logic_vector(CTRL.IDENT, 4);
   buffer_space := conv_std_logic_vector(CTRL.BUFFER_SPACE, 8);
 
   if(CTRL.TTYPE = 0) then

     data         := CTRL.DATA(15 downto 0);

     cb_packet_data    <= ident & "0000" & buffer_space;
     cb_packet_sop     <= '0';
     cb_packet_eop     <= '1';
     cb_packet_fifo_we <= '1';
     wait until (cb_packet_fifo_full = '0' and CB_CLK'event and CB_CLK='1');
     cb_packet_data    <= data;
     cb_packet_sop     <= '1';
     cb_packet_eop     <= '0';
     cb_packet_fifo_we <= '1';

     BUSY <= '0';
     wait until (cb_packet_fifo_full = '0' and CB_CLK'event and CB_CLK='1');
   else
     
     cb_packet_data    <= ident & "0000" & buffer_space;
     cb_packet_sop     <= '0';
     cb_packet_eop     <= '1';
     cb_packet_fifo_we <= '1';
     wait until (cb_packet_fifo_full = '0' and CB_CLK'event and CB_CLK='1');

      for i in 1 to 7 loop

        data         := CTRL.DATA(i*16 - 1 downto (i-1)*16);

        cb_packet_data    <= data;
        cb_packet_sop     <= '1';
        cb_packet_eop     <= '1';
        cb_packet_fifo_we <= '1';
        wait until (cb_packet_fifo_full = '0' and CB_CLK'event and CB_CLK='1');
     end loop;

     data         := CTRL.DATA(127 downto 112);

     cb_packet_data    <= data;
     cb_packet_sop     <= '1';
     cb_packet_eop     <= '0';
     cb_packet_fifo_we <= '1';
     wait until (cb_packet_fifo_full = '0' and CB_CLK'event and CB_CLK='1');

   end if;

     cb_packet_data    <= X"0000";
     cb_packet_sop     <= '1';
     cb_packet_eop     <= '1';
     cb_packet_fifo_we <= '0';

end loop;  


end process;

end architecture CB_SIM_ARCH;

