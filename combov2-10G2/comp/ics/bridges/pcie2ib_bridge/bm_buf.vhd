--
-- bm_buf.vhd : Bus Master Buffer
-- Copyright (C) 2007 CESNET
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

library IEEE;  
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use WORK.math_pack.all;
use work.ib_pkg.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                   ENTITY DECLARATION -- Bus Master Buffer                 -- 
-- ----------------------------------------------------------------------------

entity BM_BUF is 
   port (
      -- clock & reset --------------------------------------------------------
      CLK            : in std_logic;    -- FPGA clock
      RESET          : in std_logic;    -- Reset active high

      -- Bus Master interface -------------------------------------------------
      BM             : inout t_ibbm_64; -- Internal Bus BM

      -- TX and RX Buffer interface -------------------------------------------
      -- Output --
      B_M_GLOBAL_ADDR : out std_logic_vector(63 downto 0);  -- Global Address 
      B_M_LOCAL_ADDR  : out std_logic_vector(31 downto 0);  -- Local Address
      B_M_LENGTH      : out std_logic_vector(11 downto 0);  -- Length
      B_M_TAG         : out std_logic_vector(15 downto 0);  -- Operation TAG
        
      B_M_REQ_R       : out std_logic;                      -- Read Request  (for TX buffer)
      B_M_REQ_W       : out std_logic;                      -- Write Request (for RX buffer)     
                  
      -- Input --
      B_M_ACK_R       : in std_logic;                       -- Read Request accepted  (from TX buffer)
      B_M_ACK_W       : in std_logic;                       -- Write Request accepted (from RX buffer)        

      B_M_FULL_R      : in std_logic;                       -- Full buffer for read  (from TX buffer)
      B_M_FULL_W      : in std_logic;                       -- Full buffer for write (from RX buffer)      
        
      B_M_OP_TAG_R    : in std_logic_vector(15 downto 0);   -- Read operation TAG  (from RX buffer)
      B_M_OP_TAG_W    : in std_logic_vector(15 downto 0);   -- Write operation TAG (from TX buffer)    
        
      B_M_OP_DONE_R   : in std_logic;                       -- Read operation DONE  (from RX buffer)
      B_M_OP_DONE_W   : in std_logic                        -- Write operation DONE (from TX buffer)
   );
end BM_BUF;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  Bus Master Buffer              --
-- ----------------------------------------------------------------------------

architecture bm_buf_arch of BM_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_IDLE, S_RESET_R, S_RESET_W, S_DISCARD);
   signal present_state, next_state : fsm_states; 

   signal op_tag_r_reg    : std_logic_vector(15 downto 0);
   signal op_done_r_reg   : std_logic;
   signal op_tag_w_reg    : std_logic_vector(15 downto 0);
   signal op_done_w_reg   : std_logic;   
   signal r_rst           : std_logic;
   signal w_rst           : std_logic;
   signal ack_discard     : std_logic;
   signal B_M_REQ_R_aux   : std_logic;   
   signal B_M_REQ_W_aux   : std_logic;
   signal reg_full_r      : std_logic;   
   signal reg_full_w      : std_logic;
   
begin

   -- -------------------------------------------------------------------------
   --           BUS MASTER INTERFACE --> TX and RX BUFFER INTERFACE          --
   -- ------------------------------------------------------------------------- 

   B_M_GLOBAL_ADDR <= BM.GLOBAL_ADDR;  
   B_M_LOCAL_ADDR  <= BM.LOCAL_ADDR; 
   B_M_LENGTH      <= BM.LENGTH;     
   B_M_TAG         <= BM.TAG;        
                     
   B_M_REQ_R_aux   <= BM.REQ and (not BM.TRANS_TYPE(0)) and (not BM.TRANS_TYPE(1));      
   B_M_REQ_W_aux   <= BM.REQ and      BM.TRANS_TYPE(0)  and (not BM.TRANS_TYPE(1));      
   
   B_M_REQ_R       <= B_M_REQ_R_aux and (not reg_full_r);
   B_M_REQ_W       <= B_M_REQ_W_aux and (not reg_full_w);

   -- FULL logic --------------------------------------------------------------
   reg_full_rp: process(RESET, CLK, B_M_FULL_R)  
   begin
     if (RESET = '1' or B_M_FULL_R = '0') then
        reg_full_r <= '0'; 
     elsif (CLK'event AND CLK = '1') then
        if (B_M_FULL_R  = '1' and B_M_ACK_R = '1') then
           reg_full_r <= '1';
        end if;
     end if;
   end process; 

   reg_full_wp: process(RESET, CLK, B_M_FULL_W)  
   begin
     if (RESET = '1' or B_M_FULL_W = '0') then
        reg_full_w <= '0'; 
     elsif (CLK'event AND CLK = '1') then
        if (B_M_FULL_W  = '1' and B_M_ACK_W = '1') then
           reg_full_w <= '1';
        end if;
     end if;
   end process;
   
   -- -------------------------------------------------------------------------                                                         
   --           TX and RX BUFFER INTERFACE --> BUS MASTER INTERFACE          --                                                         
   -- -------------------------------------------------------------------------                                                     
                                                                                                                                    
   -- synchronize logic -------------------------------------------------------                                                                                         
   synchlogp : process(RESET, CLK)                                                                                                  
   begin                                                                                                                            
      if (RESET = '1') then                                                                                                         
         present_state <= S_IDLE;                                                                              
      elsif (CLK'event and CLK = '1') then                                                                     
         present_state <= next_state;                                                                           
      end if;                                                                                                  
   end process;                                                                                                

   -- next state logic --------------------------------------------------------                                                                                           
   nextstatelogicp : process(present_state, op_done_r_reg, op_done_w_reg,B_M_REQ_R_aux, B_M_REQ_W_aux, BM.REQ)    
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               
                                                                                                                  
         when  S_IDLE =>                                                                                          
                  if (op_done_w_reg = '1') then
                     next_state <= S_RESET_W;
                  elsif (op_done_r_reg = '1') then
                     next_state <= S_RESET_R;
                  elsif (B_M_REQ_R_aux = '0' and B_M_REQ_W_aux = '0' and BM.REQ = '1') then
                     next_state <= S_DISCARD;
                  end if;

         when  S_RESET_W =>
                     next_state <= S_IDLE;

         when  S_RESET_R =>
                     next_state <= S_IDLE;                     

         when  S_DISCARD =>
                     next_state <= S_IDLE;                      
                                   
      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state,op_done_r_reg, op_done_w_reg)
   begin                                                                                                                 
        
      w_rst       <= '0';
      r_rst       <= '0';
      BM.OP_DONE  <= '0';
      BM.OP_TAG   <= "0000000000000000"; 
      ack_discard <= '0';      
                                                                                                                                        
      case (present_state) is                                                                                     
                                                                                                                   
         when  S_IDLE =>                                                                                          
                  if (op_done_w_reg = '1') then
                     BM.OP_DONE <= '1';
                     BM.OP_TAG  <= op_tag_w_reg;
                  elsif (op_done_r_reg = '1') then
                     BM.OP_DONE <= '1';
                     BM.OP_TAG  <= op_tag_r_reg;
                  end if;

         when S_RESET_W =>
                     w_rst <= '1';

         when S_RESET_R =>
                     r_rst <= '1';

         when  S_DISCARD =>
                  ack_discard <= '1';
                  BM.OP_DONE  <= '1';
                  BM.OP_TAG   <= BM.TAG;

      end case;                                                                                                   
   end process;                                                                                                   
                                                                                                                  
   -- op_tag and op_done registers --------------------------------------------                                   
   read_op_tag_donep: process(RESET, CLK, r_rst)                                                                         
   begin
     if (RESET = '1' or r_rst = '1') then
        op_tag_r_reg  <= (others => '0'); 
        op_done_r_reg <= '0'; 
     elsif (CLK'event AND CLK = '1') then
        if (B_M_OP_DONE_R  = '1') then
           op_tag_r_reg  <= B_M_OP_TAG_R;
           op_done_r_reg <= '1';
        end if;
     end if;
   end process;   

   write_op_tag_donep: process(RESET, CLK, w_rst)  
   begin
     if (RESET = '1' or w_rst = '1') then
        op_tag_w_reg  <= (others => '0'); 
        op_done_w_reg <= '0'; 
     elsif (CLK'event AND CLK = '1') then
        if (B_M_OP_DONE_W  = '1') then
           op_tag_w_reg  <= B_M_OP_TAG_W;
           op_done_w_reg <= '1';
        end if;
     end if;
   end process;      

   -- BM.ACK multiplexor ------------------------------------------------------   
   BM.ACK <= '1'       when  ack_discard = '1' else
             B_M_ACK_R when (BM.TRANS_TYPE(0) = '0' and BM.TRANS_TYPE(1) = '0') else
             B_M_ACK_W;
             
end bm_buf_arch;

                      

