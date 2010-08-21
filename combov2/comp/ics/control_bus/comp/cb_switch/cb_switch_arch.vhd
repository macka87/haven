--
-- cb_switch_arch.vhd: Control Bus Switch
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
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB_SWITCH_ARCH of CB_SWITCH is

   -- Input maping
   type t_port_data is array(1 + DS_PORTS - 1 downto 0) of std_logic_vector(DATA_WIDTH-1 downto 0);
   signal port_in_data_in          : t_port_data;
   signal port_in_data_vld         : std_logic_vector(1 + DS_PORTS - 1 downto 0);
   signal port_in_sop              : std_logic_vector(1 + DS_PORTS - 1 downto 0);
   signal port_in_eop              : std_logic_vector(1 + DS_PORTS - 1 downto 0);
   signal port_in_dst_rdy          : std_logic_vector(1 + DS_PORTS - 1 downto 0);
  
   -- PortX_IN_DST_RDY pipeline (For Data Vld)
   signal port_in_dst_rdy_pipe   : std_logic_vector(1 + DS_PORTS - 1 downto 0);
   
   -- Shift reg
   signal port_shift_we          : std_logic_vector(1 + DS_PORTS - 1 downto 0);
   
   -- Output Data Multiplexor Signals
   signal port0_mux_sel          : std_logic_vector(LOG2(DS_PORTS) - 1 downto 0);
      
   -- Output FSM Interface
   signal ds_send_rq             : std_logic_vector(DS_PORTS-1 downto 0);
   signal ds_send_ack            : std_logic_vector(DS_PORTS-1 downto 0); -- before portX_send_ack
   signal port_fsm_rdy           : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_send_sop          : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_send_eop          : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_send_data_vld     : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_send_data         : t_port_data;
   
   -- Output Data
   signal port_out_data          : t_port_data;
   signal port_out_sop           : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_out_eop           : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_out_src_rdy       : std_logic_vector(1 + DS_PORTS-1 downto 0);
   signal port_out_dst_rdy       : std_logic_vector(1 + DS_PORTS-1 downto 0);
   
   signal sig_downstream_dst_rdy : std_logic;

   -- mux interface
   signal mx_ds_data_in         : std_logic_vector(DS_PORTS*DATA_WIDTH-1 downto 0);
   signal mx_ds_data_out        : std_logic_vector(DS_PORTS*DATA_WIDTH-1 downto 0);

begin

port_in_data_in(0)     <= PORT0.DOWN.data;
port_in_data_vld(0)    <= not PORT0.DOWN.src_rdy_n and port_in_dst_rdy_pipe(0);
port_in_sop(0)         <= not PORT0.DOWN.sop_n;
port_in_eop(0)         <= not PORT0.DOWN.eop_n;

DS_MAP: for i in 0 to DS_PORTS-1 generate
   port_in_data_in(i + 1)     <= DS_IN((i+1)*(DATA_WIDTH + 3)-1 downto i*(DATA_WIDTH + 3) + 3);
   port_in_data_vld(i + 1)    <= not DS_IN(i*(DATA_WIDTH + 3) + 0) and port_in_dst_rdy_pipe(i + 1);
   port_in_sop(i + 1)         <= not DS_IN(i*(DATA_WIDTH + 3) + 2);
   port_in_eop(i + 1)         <= not DS_IN(i*(DATA_WIDTH + 3) + 1);
end generate;



-- register dst_rdy_pipe ------------------------------------------------------
dst_rdy_pipep: process(CB_RESET, CB_CLK)
begin
   if (CB_RESET = '1') then
      for i in 0 to DS_PORTS loop
         port_in_dst_rdy_pipe(i) <= '0';
      end loop;
   elsif (CB_CLK'event AND CB_CLK = '1') then
      for i in 0 to DS_PORTS loop
         port_in_dst_rdy_pipe(i) <= port_in_dst_rdy(i);
      end loop;
   end if;
end process;

-------------------------------------------------------------------------------
--                            SHIFT REGISTERS 
-------------------------------------------------------------------------------
SHR: for i in 0 to DS_PORTS generate
   -- --- Shift Register ------------------------------------------------------
   CB_SHIFT_REG_U : entity work.IB_SHIFT_REG
   generic map (
      DATA_WIDTH   => 16
   )
   port map (
      -- Common Interface
      CLK          => CB_CLK,
      RESET        => CB_RESET,

      DATA_IN      => port_in_data_in(i),
      DATA_IN_VLD  => port_in_data_vld(i),
      SOP_IN       => port_in_sop(i),
      EOP_IN       => port_in_eop(i),
      WR_EN        => port_shift_we(i),
      DST_RDY      => port_in_dst_rdy(i),
     
      DATA_OUT     => port_send_data(i),
      DATA_OUT_VLD => port_send_data_vld(i),
      SOP_OUT      => port_send_sop(i),
      EOP_OUT      => port_send_eop(i),
      OUT_FSM_RDY  => port_fsm_rdy(i)
      
   );
end generate;

port_fsm_rdy(0) <= '1'; -- PORT0 out is always ready

-- port_out_dst_rdy(1) and port_out_dst_rdy(2) and ... and port_out_dst_rdy(DS_PORTS)
sig_downstream_dst_rdy <= '1' when port_out_dst_rdy(DS_PORTS downto 1) = conv_std_logic_vector((2**DS_PORTS) - 1, DS_PORTS) else '0';

------------------------------------------------------------------------------
-- --- INPUT FSM -------------------------------------------------------------
------------------------------------------------------------------------------

port_shift_we(0) <= sig_downstream_dst_rdy;

CB_SWITCH_IN_FSM_G: for i in 1 to DS_PORTS generate

   CB_SWITCH_IN_FSM : entity work.CB_SWITCH_IN_FSM
   port map (
   -- Common Interface

   CLK             => CB_CLK,
   RESET           => CB_RESET,

   -- BUS IN Interface
   DATA_VLD        => port_in_data_vld(i),
   DST_RDY         => open,
   SOP             => port_in_sop(i),
   EOP             => port_in_eop(i),

   -- SH_REG_WE
   SHREG_WE        => port_shift_we(i),

   -- Interface RQ
   IF_RQ           => ds_send_rq(i - 1),
   IF_ACK          => ds_send_ack(i - 1),

   -- Interface Status
   
   IF_RDY          => port_out_dst_rdy(i)
 
   );
end generate; 
 
                                                                 
-------------------------------------------------------------------------------
--                          OUTPUT MULTIPLEXOR
-------------------------------------------------------------------------------

MUX_DS_G: for i in 0 to DS_PORTS-1 generate
   mx_ds_data_in((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) <= port_send_data(i + 1);
   port_out_data(i + 1) <=  mx_ds_data_out((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH);
end generate;

-- --- CB Output Multiplexor --------------------------------------------------
CB_SWITCH_MUX_U : entity work.CB_SWITCH_MUX
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      DS_PORTS    => DS_PORTS
   )
   port map (
   
   -- Upstream
   PORT0_DATA_IN => port_send_data(0),
   PORT0_DATA_OUT => port_out_data(0),
  
   -- Downstream
   DS_DATA_IN => mx_ds_data_in,
   DS_DATA_OUT => mx_ds_data_out,
   
   PORT0_MUX_SEL  => port0_mux_sel
   
  );


-------------------------------------------------------------------------------
--                             OUTPUT FSM
-------------------------------------------------------------------------------

-- --- Output FSM -------------------------------------------------------------
CB_SWITCH_OUT_FSM_U : entity work.CB_SWITCH_OUT_FSM
   generic map(
      DS_PORTS     => DS_PORTS
   )
   port map (
   -- Common Interface
   CLK             => CB_CLK,
   RESET           => CB_RESET,

   -- Downstream ports
   DS_SEND_RQ      => ds_send_rq,
   DS_SEND_ACK     => ds_send_ack,
   DS_DATA_VLD     => port_send_data_vld(DS_PORTS downto 1),
   DS_SOP          => port_send_sop(DS_PORTS downto 1),
   DS_EOP          => port_send_eop(DS_PORTS downto 1),
   DS_FSM_RDY      => port_fsm_rdy(DS_PORTS downto 1),

   -- Output control Interface
   MUX_SEL            => port0_mux_sel,
   DST_RDY            => port_out_dst_rdy(0),
   SRC_RDY            => port_out_src_rdy(0),
   SOP                => port_out_sop(0),
   EOP                => port_out_eop(0)
   );

OUT_SOP_EOP_G: for i in 1 to DS_PORTS generate

   port_out_sop(i) <= port_send_data_vld(0) and port_send_sop(0);
   port_out_eop(i) <= port_send_data_vld(0) and port_send_eop(0);
   
   port_out_src_rdy(i) <= port_send_data_vld(0); --POSSIBLE MISSTAKE

end generate;
  
-------------------------------------------------------------------------------
--                          OUTPUT REGISTERS
-------------------------------------------------------------------------------

-- register output_registers --------------------------------------------------
output_registersp: process(CB_RESET, CB_CLK)
begin
   if (CB_RESET = '1') then

      PORT0.UP.data       <= (others => '0');
      PORT0.UP.sop_n      <= '1';
      PORT0.UP.eop_n      <= '1';
      PORT0.UP.src_rdy_n  <= '1';
      PORT0.DOWN.dst_rdy_n   <= '1';

      for i in 0 to DS_PORTS-1 loop
         ds_out((i+1)*(DATA_WIDTH + 3)-1 downto i*(DATA_WIDTH + 3) + 3)  <= (others => '0');
         ds_out(i*(DATA_WIDTH + 3) + 2)                              <= '1'; --sop
         ds_out(i*(DATA_WIDTH + 3) + 1)                              <= '1'; --eop
         ds_out(i*(DATA_WIDTH + 3) + 0)                              <= '1'; --src_rdy
         ds_in_rd(i)                                                 <= '1';
      end loop;
      
   elsif (CB_CLK'event AND CB_CLK = '1') then
      
      PORT0.DOWN.dst_rdy_n  <= not port_in_dst_rdy(0);   
      for i in 0 to DS_PORTS-1 loop   
         ds_in_rd(i) <= not port_in_dst_rdy(i + 1);
      end loop;   
         
      if (PORT0.UP.dst_rdy_n = '0') then
         PORT0.UP.data      <= port_out_data(0);
         PORT0.UP.sop_n     <= not port_out_sop(0); -- Active in Low
         PORT0.UP.eop_n     <= not port_out_eop(0); -- Active in Low
         PORT0.UP.src_rdy_n <= not port_out_src_rdy(0); -- Active in Low
      end if;
       
      for i in 0 to DS_PORTS-1 loop 
         if (ds_out_rd(i) = '0') then
            ds_out((i+1)*(DATA_WIDTH + 3)-1 downto i*(DATA_WIDTH + 3) + 3)  <= port_out_data(i + 1);
            
            ds_out(i*(DATA_WIDTH + 3) + 2)                              <= not port_out_sop(i + 1); -- Active in Low
            ds_out(i*(DATA_WIDTH + 3) + 1)                              <= not port_out_eop(i + 1); -- Active in Low
            ds_out(i*(DATA_WIDTH + 3) + 0)                              <= not port_out_src_rdy(i + 1); -- Active in Low
            
         end if;
      end loop;
      
   end if;
   
end process;

port_out_dst_rdy(0)  <= not PORT0.UP.dst_rdy_n; -- Active in Low

DST_G: for i in 0 to DS_PORTS-1 generate
   port_out_dst_rdy(i + 1)  <= not DS_OUT_RD(i); -- Active in Low
end generate;

end architecture CB_SWITCH_ARCH;
