--
-- output_fsm.vhd : IB Switch Output FSM
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.ib_ifc_pkg.all;
use work.ib_fmt_pkg.all;
use work.ib_switch_pkg.all;

-- ----------------------------------------------------------------------------
--                 ENTITY DECLARATION -- IB Switch Output FSM                --
-- ----------------------------------------------------------------------------

entity IB_SWITCH_OUTPUT_FSM is
   generic(
      -- Port number (0/1/2)
      PORT_NUM     : integer:=  0
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Upstream Port #0 (input) ---------------------------------------------
      IN0_DATA_VLD   : in  std_logic;
      IN0_SOF_N      : in  std_logic;
      IN0_EOF_N      : in  std_logic;
      IN0_RD         : out std_logic;

      IN0_REQ        : in  std_logic;
      IN0_ACK        : out std_logic;

      -- Downstream Port #1 (input) -------------------------------------------
      IN1_DATA_VLD   : in  std_logic;
      IN1_SOF_N      : in  std_logic;
      IN1_EOF_N      : in  std_logic;
      IN1_RD         : out std_logic;
                          
      IN1_REQ        : in  std_logic;
      IN1_ACK        : out std_logic;
 
      -- Downstream Port #2 ---------------------------------------------------
      IN2_DATA_VLD   : in  std_logic;
      IN2_SOF_N      : in  std_logic;
      IN2_EOF_N      : in  std_logic;
      IN2_RD         : out std_logic;
                          
      IN2_REQ        : in  std_logic;
      IN2_ACK        : out std_logic;

      -- OUTPUT Port ----------------------------------------------------------
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic;

      -- OUTPUT data control --------------------------------------------------
      MX_SEL        : out std_logic_vector(1 downto 0)
   );
end IB_SWITCH_OUTPUT_FSM;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Switch Output FSM           --
-- ----------------------------------------------------------------------------

architecture ib_switch_output_fsm_arch of IB_SWITCH_OUTPUT_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   -- FSM types and signals ---------------------------------------------------
   type   fsm_states is (S_ARBITER, S_DATA);
   signal present_state, next_state : fsm_states;

   -- Auxiliary signals -------------------------------------------------------
   signal rd0             : std_logic;
   signal rd1             : std_logic;
   signal rd2             : std_logic;

   signal ack0            : std_logic;
   signal ack1            : std_logic;
   signal ack2            : std_logic;

   signal sof_n_mux       : std_logic;
   signal eof_n_mux       : std_logic;
   signal data_vld_mux    : std_logic;

   signal priority_dec_en : std_logic;
   signal src_rdy_n       : std_logic;
   signal data_sel        : std_logic_vector(1 downto 0);
   
   signal ack_sel         : std_logic_vector(2 downto 0);
   signal ack_vec         : std_logic_vector(2 downto 0);
   signal ack_vec_reg     : std_logic_vector(2 downto 0);
   signal transaction_ack : std_logic;
   signal drop_ack        : std_logic;
   
   signal drop_reg        : std_logic;
  
begin

   -- -------------------------------------------------------------------------
   --                            OUTPUT INTERFACE                            --
   -- -------------------------------------------------------------------------
   
   IN0_ACK       <= ack0;
   IN1_ACK       <= ack1;
   IN2_ACK       <= ack2;
   
   OUT_SOF_N     <= sof_n_mux or not data_vld_mux or src_rdy_n;
   OUT_EOF_N     <= eof_n_mux or not data_vld_mux or src_rdy_n;
   OUT_SRC_RDY_N <= src_rdy_n;
   
   MX_SEL        <= data_sel;

   -- -------------------------------------------------------------------------
   --                            MULTIPLEXORS LOGIC                          --
   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- MX SELECTOR logic (ack_sel) ---------------------------------------------
   ack_vec_regp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            ack_vec_reg <= (others => '0');
         elsif (transaction_ack = '1') then
            ack_vec_reg <= ack_vec;
         end if;
      end if;
   end process;
   
   GEN_ACK_VEC0: if (PORT_NUM = 0) generate
      ack_vec <= ack2 & ack1 & '0';
   end generate;
   
   GEN_ACK_VEC1: if (PORT_NUM = 1) generate
      ack_vec <= ack2 & '0' & ack0;
   end generate;
   
   GEN_ACK_VEC2: if (PORT_NUM = 2) generate
      ack_vec <= '0' & ack1 & ack0;
   end generate;
   
   with transaction_ack select ack_sel <= ack_vec     when '1',
                                          ack_vec_reg when others;

   -- -------------------------------------------------------------------------
   -- DATA SELECTOR multiplexor -----------------------------------------------
   GEN_DEC_MUX0: if (PORT_NUM = 0) generate
      dec_muxp: process(ack_sel)
      begin
         case ack_sel is
            when "010"  => data_sel <= "01";
            when "100"  => data_sel <= "10";
            when others => data_sel <= (others => 'X');
         end case;
      end process;
   end generate;
   
   GEN_DEC_MUX1: if (PORT_NUM = 1) generate
      dec_muxp: process(ack_sel)
      begin
         case ack_sel is
            when "001"  => data_sel <= "00";
            when "100"  => data_sel <= "10";
            when others => data_sel <= (others => 'X');
         end case;
      end process;
   end generate;
   
   GEN_DEC_MUX2: if (PORT_NUM = 2) generate
      dec_muxp: process(ack_sel)
      begin
         case ack_sel is
            when "001"  => data_sel <= "00";
            when "010"  => data_sel <= "01";
            when others => data_sel <= (others => 'X');
         end case;
      end process;
   end generate;
   
   -- -------------------------------------------------------------------------
   -- DATA_VLD multiplexor ----------------------------------------------------
   data_vld_muxp: process(ack_sel, IN1_DATA_VLD, IN2_DATA_VLD, IN0_DATA_VLD)
   begin
      case ack_sel is
         when "001" => data_vld_mux <= IN0_DATA_VLD;
         when "010" => data_vld_mux <= IN1_DATA_VLD;
         when "100" => data_vld_mux <= IN2_DATA_VLD;
         when others => data_vld_mux <= '0';
      end case;
   end process;
   
   -- -------------------------------------------------------------------------
   -- SOF_N multiplexor -------------------------------------------------------
   sof_muxp: process(ack_sel, IN1_SOF_N, IN2_SOF_N, IN0_SOF_N)
   begin
      case ack_sel is
         when "001" =>  sof_n_mux <= IN0_SOF_N;
         when "010" =>  sof_n_mux <= IN1_SOF_N;
         when "100" =>  sof_n_mux <= IN2_SOF_N;
         when others => sof_n_mux <= '1';
      end case;
   end process;

   -- -------------------------------------------------------------------------
   -- EOF_N multiplexor -------------------------------------------------------
   eof_muxp: process(ack_sel, IN1_EOF_N, IN2_EOF_N, IN0_EOF_N)
   begin
      case ack_sel is
         when "001" =>  eof_n_mux <= IN0_EOF_N;
         when "010" =>  eof_n_mux <= IN1_EOF_N;
         when "100" =>  eof_n_mux <= IN2_EOF_N;
         when others => eof_n_mux <= '1';
      end case;
   end process;
     
   -- -------------------------------------------------------------------------
   --                             PRIORITY DECODER                           --
   -- -------------------------------------------------------------------------
   
   U_ib_switch_output_priority_dec: entity work.IB_SWITCH_OUTPUT_PRIORITY_DEC
   generic map (
     -- Port number (0/1/2)
     PORT_NUM      => PORT_NUM
   )
   port map (
      -- Common interface --
      CLK          => CLK,
      RESET        => RESET,
      ENABLE       => priority_dec_en,
      
      -- Input Request Interface --
      PORT0_REQ    => IN0_REQ,
      PORT1_REQ    => IN1_REQ,
      PORT2_REQ    => IN2_REQ,
      
      -- Output Acknowledge Interface --
      PORT0_ACK    => ack0,
      PORT1_ACK    => ack1,
      PORT2_ACK    => ack2
   );

   GEN_TRANS_ACK0: if (PORT_NUM = 0) generate
      transaction_ack <= ack1 or ack2;
      drop_ack        <= ack0;
   end generate;
   
   GEN_TRANS_ACK1: if (PORT_NUM = 1) generate
      transaction_ack <= ack0 or ack2;
      drop_ack        <= ack1;
   end generate;
   
   GEN_TRANS_ACK2: if (PORT_NUM = 2) generate
      transaction_ack <= ack0 or ack1;
      drop_ack        <= ack2;
   end generate;

   -- -------------------------------------------------------------------------
   --                               CONTROL FSM                              --
   -- -------------------------------------------------------------------------
 
   -- -------------------------------------------------------------------------
   -- synchronize logic -------------------------------------------------------
   synchlogp : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            present_state <= S_ARBITER;
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- next state logic --------------------------------------------------------
   nextstatelogicp : process(present_state, transaction_ack, eof_n_mux, data_vld_mux, OUT_DST_RDY_N, drop_ack)
   begin
      next_state <= present_state;
      
      case (present_state) is
           
         -- S_ARBITER ---------------------------------------------------------
         when  S_ARBITER =>
            if (transaction_ack = '1') then
               if (eof_n_mux = '0' and data_vld_mux = '1' and OUT_DST_RDY_N = '0') then
                  next_state <= S_ARBITER;
               else
                  next_state <= S_DATA;
               end if;
            end if;

         -- S_DATA ------------------------------------------------------------
         when  S_DATA =>
               if (eof_n_mux = '0' and data_vld_mux = '1' and OUT_DST_RDY_N = '0') then
                  next_state <= S_ARBITER;
               else
                  next_state <= S_DATA;
               end if;
         
      end case;
   end process;
    
   -- -------------------------------------------------------------------------
   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state, transaction_ack, eof_n_mux, data_vld_mux, OUT_DST_RDY_N, drop_ack, sof_n_mux, ack_sel)
   begin
      priority_dec_en <= '0';
      src_rdy_n       <= '1';
      rd0             <= '0';
      rd1             <= '0';
      rd2             <= '0';

      case (present_state) is
      
         -- S_ARBITER ---------------------------------------------------------
         when  S_ARBITER =>
            if (OUT_DST_RDY_N = '0') then
               priority_dec_en <= '1';
            end if;

            if (transaction_ack = '1') then
               if (data_vld_mux = '1' and sof_n_mux = '0') then
                  src_rdy_n <= '0';
                  
                  rd0 <= not OUT_DST_RDY_N and ack_sel(0);
                  rd1 <= not OUT_DST_RDY_N and ack_sel(1);
                  rd2 <= not OUT_DST_RDY_N and ack_sel(2);
               end if;
            end if;

         -- S_DATA ------------------------------------------------------------
         when  S_DATA =>
               if (data_vld_mux = '1') then
                  src_rdy_n <= '0';
                  
                  rd0 <= not OUT_DST_RDY_N and ack_sel(0);
                  rd1 <= not OUT_DST_RDY_N and ack_sel(1);
                  rd2 <= not OUT_DST_RDY_N and ack_sel(2);
               end if;
        
      end case;
   end process;
   
   -- -------------------------------------------------------------------------
   --                             DROP CONTROL
   -- -------------------------------------------------------------------------
   drop_regp: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            drop_reg <= '0';
         elsif ((PORT_NUM = 0 and IN0_EOF_N = '0' and IN0_DATA_VLD = '1') or
                (PORT_NUM = 1 and IN1_EOF_N = '0' and IN1_DATA_VLD = '1') or
                (PORT_NUM = 2 and IN2_EOF_N = '0' and IN2_DATA_VLD = '1')) then
            drop_reg <= '0';
         elsif (drop_ack = '1') then
            drop_reg <= '1';
         end if;
      end if;
   end process;
   
   GEN_RD0: if (PORT_NUM = 0) generate
      IN0_RD <= drop_ack or drop_reg;
      IN1_RD <= rd1;
      IN2_RD <= rd2;
   end generate;
   
   GEN_RD1: if (PORT_NUM = 1) generate
      IN0_RD <= rd0;
      IN1_RD <= drop_ack or drop_reg;
      IN2_RD <= rd2;
   end generate;
   
   GEN_RD2: if (PORT_NUM = 2) generate
      IN0_RD <= rd0;
      IN1_RD <= rd1;
      IN2_RD <= drop_ack or drop_reg;
   end generate;
   
end ib_switch_output_fsm_arch;



