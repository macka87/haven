--
-- ib_switch_arch.vhd: Internal Bus Switch
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_CORE_ARCH of IB_SWITCH_CORE is

   -- Input Addres, Data Lenght, Transaction Type
   signal port0_in_dst_addr         : std_logic_vector(31 downto 0);
   signal port1_in_dst_addr         : std_logic_vector(31 downto 0);
   signal port2_in_dst_addr         : std_logic_vector(31 downto 0);
   signal port0_in_trans_type       : std_logic_vector(C_IB_TRANS_TYPE_WIDTH-1 downto 0);
   signal port1_in_trans_type       : std_logic_vector(C_IB_TRANS_TYPE_WIDTH-1 downto 0);
   signal port2_in_trans_type       : std_logic_vector(C_IB_TRANS_TYPE_WIDTH-1 downto 0);

   -- Input maping
   signal port0_in_data_in          : std_logic_vector(63 downto 0);
   signal port0_in_data_vld         : std_logic;
   signal port0_in_sop              : std_logic;
   signal port0_in_eop              : std_logic;
   signal port0_in_dst_rdy          : std_logic;
   signal port1_in_data_in          : std_logic_vector(63 downto 0);
   signal port1_in_data_vld         : std_logic;
   signal port1_in_sop              : std_logic;
   signal port1_in_eop              : std_logic;
   signal port1_in_dst_rdy          : std_logic;
   signal port2_in_data_in          : std_logic_vector(63 downto 0);
   signal port2_in_data_vld         : std_logic;
   signal port2_in_sop              : std_logic;
   signal port2_in_eop              : std_logic;
   signal port2_in_dst_rdy          : std_logic;
   
   -- PortX_IN_DST_RDY pipeline (For Data Vld)
   signal port0_in_dst_rdy_pipe  : std_logic;
   signal port1_in_dst_rdy_pipe  : std_logic;
   signal port2_in_dst_rdy_pipe  : std_logic;
   
   -- Address Decoder Signals
   signal port0_addr_dec_match   : std_logic;
   signal port1_addr_dec_match   : std_logic;
   signal port2_addr_dec_match   : std_logic;
   signal port0_if_select        : std_logic_vector(2 downto 0);
   signal port1_if_select        : std_logic_vector(2 downto 0);
   signal port2_if_select        : std_logic_vector(2 downto 0);
      
   -- Shift reg
   signal port0_shr_wr_en        : std_logic;
   signal port1_shr_wr_en        : std_logic;
   signal port2_shr_wr_en        : std_logic;
   
   -- Output Data Multiplexor Signals
   signal port0_mux_sel          : std_logic_vector(1 downto 0);
   signal port1_mux_sel          : std_logic_vector(1 downto 0);
   signal port2_mux_sel          : std_logic_vector(1 downto 0);
      
   -- Output FSM Interface
   signal port0_send_rq          : std_logic_vector(2 downto 0);
   signal port1_send_rq          : std_logic_vector(2 downto 0);
   signal port2_send_rq          : std_logic_vector(2 downto 0);
   signal port0_send_ack         : std_logic_vector(2 downto 0);
   signal port1_send_ack         : std_logic_vector(2 downto 0);
   signal port2_send_ack         : std_logic_vector(2 downto 0);
   signal port0_send_rdy         : std_logic;
   signal port1_send_rdy         : std_logic;
   signal port2_send_rdy         : std_logic;
   signal port0_fsm_rdy          : std_logic_vector(2 downto 0);
   signal port1_fsm_rdy          : std_logic_vector(2 downto 0);
   signal port2_fsm_rdy          : std_logic_vector(2 downto 0);
   signal port0_send_eop         : std_logic;
   signal port1_send_eop         : std_logic;
   signal port2_send_eop         : std_logic;
   signal port0_send_sop         : std_logic;
   signal port1_send_sop         : std_logic;
   signal port2_send_sop         : std_logic;
   signal port0_send_data_vld    : std_logic;
   signal port1_send_data_vld    : std_logic;
   signal port2_send_data_vld    : std_logic;
   signal port0_send_data        : std_logic_vector(63 downto 0);
   signal port1_send_data        : std_logic_vector(63 downto 0);
   signal port2_send_data        : std_logic_vector(63 downto 0);
   
   -- Output Data
   signal port0_out_data         : std_logic_vector(63 downto 0);
   signal port1_out_data         : std_logic_vector(63 downto 0);
   signal port2_out_data         : std_logic_vector(63 downto 0);
   signal port0_out_sop          : std_logic;
   signal port1_out_sop          : std_logic;
   signal port2_out_sop          : std_logic;
   signal port0_out_eop          : std_logic;
   signal port1_out_eop          : std_logic;
   signal port2_out_eop          : std_logic;
   signal port0_out_src_rdy      : std_logic;
   signal port1_out_src_rdy      : std_logic;
   signal port2_out_src_rdy      : std_logic;
   signal port0_out_dst_rdy      : std_logic;
   signal port1_out_dst_rdy      : std_logic;
   signal port2_out_dst_rdy      : std_logic;
   signal port0_pipe_flag        : std_logic;
   signal port1_pipe_flag        : std_logic;
   signal port2_pipe_flag        : std_logic;

begin

-- Input Addres, Data Lenght, Transaction Type MAPING
port0_in_dst_addr    <= PORT0_DOWN_data(63 downto 32);
port1_in_dst_addr    <= PORT1_UP_data(63 downto 32);
port2_in_dst_addr    <= PORT2_UP_data(63 downto 32);
port0_in_trans_type  <= PORT0_DOWN_data(C_IB_LENGTH_WIDTH+C_IB_TRANS_TYPE_WIDTH-1 downto C_IB_LENGTH_WIDTH);
port1_in_trans_type  <= PORT1_UP_data(C_IB_LENGTH_WIDTH+C_IB_TRANS_TYPE_WIDTH-1 downto C_IB_LENGTH_WIDTH);
port2_in_trans_type  <= PORT2_UP_data(C_IB_LENGTH_WIDTH+C_IB_TRANS_TYPE_WIDTH-1 downto C_IB_LENGTH_WIDTH);


port0_in_data_in     <= PORT0_DOWN_data;
port0_in_data_vld    <= not PORT0_DOWN_src_rdy_n and port0_in_dst_rdy_pipe;
port0_in_sop         <= not PORT0_DOWN_sop_n;
port0_in_eop         <= not PORT0_DOWN_eop_n;
port1_in_data_in     <= PORT1_UP_data;
port1_in_data_vld    <= not PORT1_UP_src_rdy_n and port1_in_dst_rdy_pipe;
port1_in_sop         <= not PORT1_UP_sop_n;
port1_in_eop         <= not PORT1_UP_eop_n;
port2_in_data_in     <= PORT2_UP_data;
port2_in_data_vld    <= not PORT2_UP_src_rdy_n and port2_in_dst_rdy_pipe;
port2_in_sop         <= not PORT2_UP_sop_n;
port2_in_eop         <= not PORT2_UP_eop_n;


-- register dst_rdy_pipe ------------------------------------------------------
dst_rdy_pipep: process(IB_RESET, IB_CLK)
begin
   if (IB_RESET = '1') then
      port0_in_dst_rdy_pipe <= '0';
      port1_in_dst_rdy_pipe <= '0';
      port2_in_dst_rdy_pipe <= '0';
   elsif (IB_CLK'event AND IB_CLK = '1') then
      port0_in_dst_rdy_pipe <= port0_in_dst_rdy;
      port1_in_dst_rdy_pipe <= port1_in_dst_rdy;
      port2_in_dst_rdy_pipe <= port2_in_dst_rdy;
   end if;
end process;


-------------------------------------------------------------------------------
--                              ADDRESS DECODERS
-------------------------------------------------------------------------------

-- --- Address decoder port0 --------------------------------------------------
IB_SWITCH_ADDR_DEC_0_U :  entity work.IB_SWITCH_ADDR_DEC
   generic map (
      -- Port 0 Address Space 
      SWITCH_BASE       => SWITCH_BASE,
      SWITCH_LIMIT      => SWITCH_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  => DOWNSTREAM0_BASE,
      DOWNSTREAM0_LIMIT => DOWNSTREAM0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  => DOWNSTREAM1_BASE,
      DOWNSTREAM1_LIMIT => DOWNSTREAM1_LIMIT,

      PORT_NO           => 0
      )
   port map (
      CLK           => IB_CLK,
      RESET         => IB_RESET,
      ADDR_IN       => port0_in_dst_addr,
      TRANS_TYPE    => port0_in_trans_type,
      IF_SELECT     => port0_if_select,
      MATCH         => port0_addr_dec_match
      );

-- --- Address decoder port1 --------------------------------------------------
IB_SWITCH_ADDR_DEC_1_U :  entity work.IB_SWITCH_ADDR_DEC
   generic map (
      -- Port 0 Address Space 
      SWITCH_BASE       => SWITCH_BASE,
      SWITCH_LIMIT      => SWITCH_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  => DOWNSTREAM0_BASE,
      DOWNSTREAM0_LIMIT => DOWNSTREAM0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  => DOWNSTREAM1_BASE,
      DOWNSTREAM1_LIMIT => DOWNSTREAM1_LIMIT,

      PORT_NO           => 1
      )
   port map (
      CLK           => IB_CLK,
      RESET         => IB_RESET,
      ADDR_IN       => port1_in_dst_addr,
      TRANS_TYPE    => port1_in_trans_type,
      IF_SELECT     => port1_if_select,
      MATCH         => port1_addr_dec_match
      );

-- --- Address decoder port2 --------------------------------------------------
IB_SWITCH_ADDR_DEC_2_U : entity work.IB_SWITCH_ADDR_DEC
   generic map (
      -- Port 0 Address Space 
      SWITCH_BASE       => SWITCH_BASE,
      SWITCH_LIMIT      => SWITCH_LIMIT,
      -- Port 1 Address Space
      DOWNSTREAM0_BASE  => DOWNSTREAM0_BASE,
      DOWNSTREAM0_LIMIT => DOWNSTREAM0_LIMIT,
      -- Port 2 Address Space
      DOWNSTREAM1_BASE  => DOWNSTREAM1_BASE,
      DOWNSTREAM1_LIMIT => DOWNSTREAM1_LIMIT,

      PORT_NO           => 2
      )
   port map (
      CLK           => IB_CLK,
      RESET         => IB_RESET,
      ADDR_IN       => port2_in_dst_addr,
      TRANS_TYPE    => port2_in_trans_type,
      IF_SELECT     => port2_if_select,
      MATCH         => port2_addr_dec_match
      );


-------------------------------------------------------------------------------
--                            SHIFT REGISTERS 
-------------------------------------------------------------------------------

port0_send_rdy <= port0_fsm_rdy(1) or port0_fsm_rdy(2);
-- --- Shift Register0 --------------------------------------------------------
IB_SHIFT_REG0_U : entity work.IB_SHIFT_REG
   generic map (
      DATA_WIDTH   => 64
      )
   port map (
      -- Common Interface
      CLK          => IB_CLK,
      RESET        => IB_RESET,

      DATA_IN      => port0_in_data_in,
      DATA_IN_VLD  => port0_in_data_vld,
      SOP_IN       => port0_in_sop,
      EOP_IN       => port0_in_eop,
      WR_EN        => port0_shr_wr_en,
      DST_RDY      => port0_in_dst_rdy,
      
      DATA_OUT     => port0_send_data,
      DATA_OUT_VLD => port0_send_data_vld,
      SOP_OUT      => port0_send_sop,
      EOP_OUT      => port0_send_eop,
      OUT_FSM_RDY  => port0_send_rdy
   );

port1_send_rdy <= port1_fsm_rdy(0) or port1_fsm_rdy(2);
-- --- Shift Register1 --------------------------------------------------------
IB_SHIFT_REG1_U : entity work.IB_SHIFT_REG
   generic map (
      DATA_WIDTH   => 64
      )
   port map (
      -- Common Interface
      CLK          => IB_CLK,
      RESET        => IB_RESET,

      DATA_IN      => port1_in_data_in,
      DATA_IN_VLD  => port1_in_data_vld,
      SOP_IN       => port1_in_sop,
      EOP_IN       => port1_in_eop,
      WR_EN        => port1_shr_wr_en,
      DST_RDY      => port1_in_dst_rdy,
      
      DATA_OUT     => port1_send_data,
      DATA_OUT_VLD => port1_send_data_vld,
      SOP_OUT      => port1_send_sop,
      EOP_OUT      => port1_send_eop,
      OUT_FSM_RDY  => port1_send_rdy
   );

port2_send_rdy <= port2_fsm_rdy(0) or port2_fsm_rdy(1);
-- --- Shift Register2 --------------------------------------------------------
IB_SHIFT_REG2_U : entity work.IB_SHIFT_REG
   generic map (
      DATA_WIDTH   => 64
      )
   port map (
      -- Common Interface
      CLK          => IB_CLK,
      RESET        => IB_RESET,

      DATA_IN      => port2_in_data_in,
      DATA_IN_VLD  => port2_in_data_vld,
      SOP_IN       => port2_in_sop,
      EOP_IN       => port2_in_eop,
      WR_EN        => port2_shr_wr_en,
      DST_RDY      => port2_in_dst_rdy,
      
      DATA_OUT     => port2_send_data,
      DATA_OUT_VLD => port2_send_data_vld,
      SOP_OUT      => port2_send_sop,
      EOP_OUT      => port2_send_eop,
      OUT_FSM_RDY  => port2_send_rdy
   );


-------------------------------------------------------------------------------
--                              INPUT FSM
-------------------------------------------------------------------------------

-- --- Input FSM 0 ------------------------------------------------------------
IB_SWITCH_IN_FSM0_U : entity work.IB_SWITCH_IN_FSM
   generic map (
      PORT_NO           => 0
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- BUS IN Interface
   DATA_VLD        => port0_in_data_vld,
   SOP             => port0_in_sop,
   EOP             => port0_in_eop,
   
   -- Address Decoder
   ADDR_DEC_MATCH  => port0_addr_dec_match,
   IF_SELECT       => port0_if_select,
   
   -- Shift Register WR Enable 
   SHR_WR_EN       => port0_shr_wr_en,
   
   -- Interface RQ
   IF_RQ           => port0_send_rq,
   IF_ACK          => port0_send_ack
   );

-- --- Input FSM 1 ------------------------------------------------------------
IB_SWITCH_IN_FSM1_U : entity work.IB_SWITCH_IN_FSM
   generic map (
      PORT_NO           => 1
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- BUS IN Interface
   DATA_VLD        => port1_in_data_vld,
   SOP             => port1_in_sop,
   EOP             => port1_in_eop,
   
   -- Address Decoder
   ADDR_DEC_MATCH  => port1_addr_dec_match,
   IF_SELECT       => port1_if_select,
   
   -- Shift Register WR Enable 
   SHR_WR_EN       => port1_shr_wr_en,
   
   -- Interface RQ
   IF_RQ           => port1_send_rq,
   IF_ACK          => port1_send_ack
   );

-- --- Input FSM 2 ------------------------------------------------------------
IB_SWITCH_IN_FSM2_U : entity work.IB_SWITCH_IN_FSM
   generic map (
      PORT_NO           => 2
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- BUS IN Interface
   DATA_VLD        => port2_in_data_vld,
   SOP             => port2_in_sop,
   EOP             => port2_in_eop,
   
   -- Address Decoder
   ADDR_DEC_MATCH  => port2_addr_dec_match,
   IF_SELECT       => port2_if_select,
   
   -- Shift Register WR Enable 
   SHR_WR_EN       => port2_shr_wr_en,
   
   -- Interface RQ
   IF_RQ           => port2_send_rq,
   IF_ACK          => port2_send_ack
   );

-------------------------------------------------------------------------------
--                          OUTPUT MULTIPLEXORS
-------------------------------------------------------------------------------

-- --- IB Output Multiplexor --------------------------------------------------
IB_SWITCH_MUX_U : entity work.IB_SWITCH_MUX
   port map (
   -- Data IN
   PORTO_DATA_IN => port0_send_data,
   PORT1_DATA_IN => port1_send_data,
   PORT2_DATA_IN => port2_send_data,
   
   -- Port 0 Data Out
   PORT0_DATA_OUT => port0_out_data,
   PORT0_MUX_SEL  => port0_mux_sel,
   
   -- Port 1 Data Out
   PORT1_DATA_OUT => port1_out_data,
   PORT1_MUX_SEL  => port1_mux_sel,
   
   -- Port 2 Data Out
   PORT2_DATA_OUT => port2_out_data,
   PORT2_MUX_SEL  => port2_mux_sel
   );


-------------------------------------------------------------------------------
--                             OUTPUT FSM
-------------------------------------------------------------------------------

-- --- Output FSM 0 -----------------------------------------------------------
IB_SWITCH_OUT_FSM0_U : entity work.IB_SWITCH_OUT_FSM
   generic map (
      PORT_NO           => 0
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- Send RQ from Port 0
   PORT0_SEND_RQ      => port0_send_rq(0),
   PORT0_SEND_ACK     => port0_send_ack(0),
   PORT0_DATA_VLD     => port0_send_data_vld,
   PORT0_SOP          => port0_send_sop,
   PORT0_EOP          => port0_send_eop,
   PORT0_FSM_RDY      => port0_fsm_rdy(0),

   -- Send RQ from Port 1
   PORT1_SEND_RQ      => port1_send_rq(0),
   PORT1_SEND_ACK     => port1_send_ack(0),
   PORT1_DATA_VLD     => port1_send_data_vld,
   PORT1_SOP          => port1_send_sop,
   PORT1_EOP          => port1_send_eop,
   PORT1_FSM_RDY      => port1_fsm_rdy(0),

   -- Send RQ from Port 2
   PORT2_SEND_RQ      => port2_send_rq(0),
   PORT2_SEND_ACK     => port2_send_ack(0),
   PORT2_DATA_VLD     => port2_send_data_vld,
   PORT2_SOP          => port2_send_sop,
   PORT2_EOP          => port2_send_eop,
   PORT2_FSM_RDY      => port2_fsm_rdy(0),

   -- Output control Interface
   MUX_SEL            => port0_mux_sel,
   DST_RDY            => port0_out_dst_rdy,
   SRC_RDY            => port0_out_src_rdy,
   SOP                => port0_out_sop,
   EOP                => port0_out_eop
   );

-- --- Output FSM 1 -----------------------------------------------------------
IB_SWITCH_OUT_FSM1_U : entity work.IB_SWITCH_OUT_FSM
   generic map (
      PORT_NO           => 1
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- Send RQ from Port 0
   PORT0_SEND_RQ      => port0_send_rq(1),
   PORT0_SEND_ACK     => port0_send_ack(1),
   PORT0_DATA_VLD     => port0_send_data_vld,
   PORT0_SOP          => port0_send_sop,
   PORT0_EOP          => port0_send_eop,
   PORT0_FSM_RDY      => port0_fsm_rdy(1),

   -- Send RQ from Port 1
   PORT1_SEND_RQ      => port1_send_rq(1),
   PORT1_SEND_ACK     => port1_send_ack(1),
   PORT1_DATA_VLD     => port1_send_data_vld,
   PORT1_SOP          => port1_send_sop,
   PORT1_EOP          => port1_send_eop,
   PORT1_FSM_RDY      => port1_fsm_rdy(1),

   -- Send RQ from Port 2
   PORT2_SEND_RQ      => port2_send_rq(1),
   PORT2_SEND_ACK     => port2_send_ack(1),
   PORT2_DATA_VLD     => port2_send_data_vld,
   PORT2_SOP          => port2_send_sop,
   PORT2_EOP          => port2_send_eop,
   PORT2_FSM_RDY      => port2_fsm_rdy(1),

   -- Output control Interface
   MUX_SEL            => port1_mux_sel,
   DST_RDY            => port1_out_dst_rdy,
   SRC_RDY            => port1_out_src_rdy,
   SOP                => port1_out_sop,
   EOP                => port1_out_eop
   );

-- --- Output FSM 2 -----------------------------------------------------------
IB_SWITCH_OUT_FSM2_U : entity work.IB_SWITCH_OUT_FSM
   generic map (
      PORT_NO           => 2
      )
   port map (
   -- Common Interface
   CLK             => IB_CLK,
   RESET           => IB_RESET,

   -- Send RQ from Port 0
   PORT0_SEND_RQ      => port0_send_rq(2),
   PORT0_SEND_ACK     => port0_send_ack(2),
   PORT0_DATA_VLD     => port0_send_data_vld,
   PORT0_SOP          => port0_send_sop,
   PORT0_EOP          => port0_send_eop,
   PORT0_FSM_RDY      => port0_fsm_rdy(2),
   
   -- Send RQ from Port 1
   PORT1_SEND_RQ      => port1_send_rq(2),
   PORT1_SEND_ACK     => port1_send_ack(2),
   PORT1_DATA_VLD     => port1_send_data_vld,
   PORT1_SOP          => port1_send_sop,
   PORT1_EOP          => port1_send_eop,
   PORT1_FSM_RDY      => port1_fsm_rdy(2),


   -- Send RQ from Port 2
   PORT2_SEND_RQ      => port2_send_rq(2),
   PORT2_SEND_ACK     => port2_send_ack(2),
   PORT2_DATA_VLD     => port2_send_data_vld,
   PORT2_SOP          => port2_send_sop,
   PORT2_EOP          => port2_send_eop,
   PORT2_FSM_RDY      => port2_fsm_rdy(2),

   -- Output control Interface
   MUX_SEL            => port2_mux_sel,
   DST_RDY            => port2_out_dst_rdy,
   SRC_RDY            => port2_out_src_rdy,
   SOP                => port2_out_sop,
   EOP                => port2_out_eop
   );
   
-------------------------------------------------------------------------------
--                          OUTPUT REGISTERS
-------------------------------------------------------------------------------

-- register output_registers --------------------------------------------------
output_registersp: process(IB_RESET, IB_CLK)
begin
   if (IB_RESET = '1') then
      PORT0_UP_data         <= (others => '0');
      PORT1_DOWN_data       <= (others => '0');
      PORT2_DOWN_data       <= (others => '0');
      PORT0_UP_sop_n        <= '1';
      PORT1_DOWN_sop_n      <= '1';
      PORT2_DOWN_sop_n      <= '1';
      PORT0_UP_eop_n        <= '1';
      PORT1_DOWN_eop_n      <= '1';
      PORT2_DOWN_eop_n      <= '1';
      PORT0_UP_src_rdy_n    <= '1';
      PORT1_DOWN_src_rdy_n  <= '1';
      PORT2_DOWN_src_rdy_n  <= '1';
      PORT0_DOWN_dst_rdy_n  <= '1';
      PORT1_UP_dst_rdy_n    <= '1';
      PORT2_UP_dst_rdy_n    <= '1';
      port0_pipe_flag       <= '0';
      port1_pipe_flag       <= '0';
      port2_pipe_flag       <= '0';
--  elsif (IB_CLK'event AND IB_CLK = '1') then
      else 
         if (IB_CLK'event AND IB_CLK = '1') then
           PORT0_DOWN_dst_rdy_n  <= not port0_in_dst_rdy;
           PORT1_UP_dst_rdy_n    <= not port1_in_dst_rdy;
           PORT2_UP_dst_rdy_n    <= not port2_in_dst_rdy;
         
           if (PORT0_UP_dst_rdy_n = '0' or port0_pipe_flag = '0') then
             port0_pipe_flag    <= port0_out_src_rdy;
             PORT0_UP_data      <= port0_out_data;
             PORT0_UP_sop_n     <= not port0_out_sop; -- Active in Low
             PORT0_UP_eop_n     <= not port0_out_eop; -- Active in Low
             PORT0_UP_src_rdy_n <= not port0_out_src_rdy; -- Active in Low
           end if;
       
           if (PORT1_DOWN_dst_rdy_n = '0' or port1_pipe_flag = '0') then
              port1_pipe_flag      <= port1_out_src_rdy;
              PORT1_DOWN_data      <= port1_out_data;
              PORT1_DOWN_sop_n     <= not port1_out_sop; -- Active in Low
              PORT1_DOWN_eop_n     <= not port1_out_eop; -- Active in Low
              PORT1_DOWN_src_rdy_n <= not port1_out_src_rdy; -- Active in Low
           end if;

           if (PORT2_DOWN_dst_rdy_n = '0' or port2_pipe_flag = '0') then
              port2_pipe_flag      <= port2_out_src_rdy;
              PORT2_DOWN_data      <= port2_out_data;
              PORT2_DOWN_sop_n     <= not port2_out_sop; -- Active in Low
              PORT2_DOWN_eop_n     <= not port2_out_eop; -- Active in Low
              PORT2_DOWN_src_rdy_n <= not port2_out_src_rdy; -- Active in Low
           end if;
        end if;
     end if;
end process;

port0_out_dst_rdy  <= not PORT0_UP_dst_rdy_n or not port0_pipe_flag; -- Active in Low
port1_out_dst_rdy  <= not PORT1_DOWN_dst_rdy_n or not port1_pipe_flag; -- Active in Low
port2_out_dst_rdy  <= not PORT2_DOWN_dst_rdy_n or not port2_pipe_flag; -- Active in Low

end architecture IB_SWITCH_CORE_ARCH;
