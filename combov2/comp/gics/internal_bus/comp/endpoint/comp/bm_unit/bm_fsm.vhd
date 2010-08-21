--
-- bm_fsm.vhd : IB Endpoint Bus Master Unit FSM
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--          ENTITY DECLARATION -- IB Endpoint Bus Master Unit FSM            --
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_BM_UNIT_FSM is 
   generic (
      -- if transaction is done in 1 clk (read or bm trans with datawidth=128)
      IN1_SHORT_TRANS   : boolean := false;
      IN2_SHORT_TRANS   : boolean := false
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  
 
      -- Input Transaction stream interface #1 --------------------------------
      IN1_SOF_N     : in  std_logic;
      IN1_EOF_N     : in  std_logic;
      IN1_SRC_RDY_N : in  std_logic;
      IN1_DST_RDY_N : out std_logic;

      -- Input Transaction stream interface #2 --------------------------------
      IN2_SOF_N     : in  std_logic;
      IN2_EOF_N     : in  std_logic;
      IN2_SRC_RDY_N : in  std_logic;
      IN2_DST_RDY_N : out std_logic;      

      -- Output Transaction stream interface ----------------------------------
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic;       
      
      OUT_MX_SEL    : out std_logic
   );
end IB_ENDPOINT_BM_UNIT_FSM;

-- ----------------------------------------------------------------------------
--        ARCHITECTURE DECLARATION  --  IB Endpoint Bus Master Unit FSM      --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_bm_unit_fsm_arch of IB_ENDPOINT_BM_UNIT_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_ARBITER, S_1, S_2);
   signal present_state, next_state : fsm_states; 
   
   signal rr_en         : std_logic;
   signal ack1,ack2     : std_logic;
   signal rr_rq1,rr_rq2 : std_logic;
   signal mx_sel        : std_logic;
begin

   -- -------------------------------------------------------------------------
   --                          OUTPUT MULTIPLEXORS                           --
   -- -------------------------------------------------------------------------
   
   out_mux_p: process (mx_sel, IN1_SOF_N, IN1_EOF_N, IN1_SRC_RDY_N,
                       IN2_SOF_N, IN2_EOF_N, IN2_SRC_RDY_N)
   begin
      if (mx_sel = '0') then
         OUT_SOF_N     <= IN1_SOF_N;
         OUT_EOF_N     <= IN1_EOF_N;
         OUT_SRC_RDY_N <= IN1_SRC_RDY_N;
      else
         OUT_SOF_N     <= IN2_SOF_N;
         OUT_EOF_N     <= IN2_EOF_N;
         OUT_SRC_RDY_N <= IN2_SRC_RDY_N;
      end if;
   end process;
   
   -- -------------------------------------------------------------------------
   --                          ROUND ROBIN ARBITER                           --
   -- -------------------------------------------------------------------------
   rr_rq1 <= not (IN1_SOF_N or IN1_SRC_RDY_N or OUT_DST_RDY_N);
   rr_rq2 <= not (IN2_SOF_N or IN2_SRC_RDY_N or OUT_DST_RDY_N);
   
   RR_ARB : entity work.RR_ARBITER
   generic map (
      PORTS       => 2
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      ENABLE      => rr_en,
      
      RQ(0)       => rr_rq1,
      RQ(1)       => rr_rq2,
      
      ACK(0)      => ack1,
      ACK(1)      => ack2
   );
   
   -- -------------------------------------------------------------------------
   --                            BUS MASTER FSM                              --
   -- -------------------------------------------------------------------------
   
   -- synchronize logic ----------------------------------------------------
   synchlogp : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then 
         if (RESET = '1') then
            present_state <= S_ARBITER; 
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   -- next state logic -----------------------------------------------------
   nextstatelogicp : process(present_state,ack1,ack2,IN1_EOF_N,IN2_EOF_N,OUT_DST_RDY_N)
   begin
      next_state <= present_state;
      
      case (present_state) is
      
         when  S_ARBITER =>
            if (ack1 = '1' and IN1_SHORT_TRANS = false) then
               next_state <= S_1;
            elsif (ack2 = '1' and IN2_SHORT_TRANS = false) then
               next_state <= S_2;
            end if;
         
         when  S_1 =>
            if ((not IN1_EOF_N and not OUT_DST_RDY_N) = '1') then
               next_state <= S_ARBITER;
            end if;
         
         when  S_2 =>
            if ((not IN2_EOF_N and not OUT_DST_RDY_N) = '1') then
               next_state <= S_ARBITER;
            end if;
         
      end case;
   end process;
   
   -- output logic ---------------------------------------------------------
   outputlogicp : process(present_state,ack1,ack2,OUT_DST_RDY_N)
   begin 

      case (present_state) is 
      
         when  S_ARBITER =>
            rr_en <= '1';
            mx_sel <= '0';
            IN1_DST_RDY_N <= '1';
            IN2_DST_RDY_N <= '1';
            if (ack1 = '1') then
               mx_sel <= '0';
               IN1_DST_RDY_N <= '0';
               IN2_DST_RDY_N <= '1';
            elsif (ack2 = '1') then
               mx_sel <= '1';
               IN1_DST_RDY_N <= '1';
               IN2_DST_RDY_N <= '0';
            end if;
            
         when  S_1 =>
            rr_en  <= '0';
            mx_sel <= '0';
            IN1_DST_RDY_N <= OUT_DST_RDY_N;
            IN2_DST_RDY_N <= '1';
         
         when  S_2 =>
            rr_en  <= '0';
            mx_sel <= '1';
            IN1_DST_RDY_N <= '1';
            IN2_DST_RDY_N <= OUT_DST_RDY_N;
         
      end case;
   end process;
   
   OUT_MX_SEL <= mx_sel;
   
end ib_endpoint_bm_unit_fsm_arch;


