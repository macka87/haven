--
-- tx_buf_align.vhd : TX Buffer data alignment block (according to dstaddr[2] for data)
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

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--            ENTITY DECLARATION -- TX Buffer data alignment                 -- 
-- ----------------------------------------------------------------------------

entity TX_BUF_ALIGN is 
   port (
      -- clock & reset --------------------------------------------------------
      CLK              : in std_logic;                      -- FPGA clock
      RESET            : in std_logic;                      -- Reset active high

      -- Internal Bus INPUT interface -----------------------------------------
      IB_IN_DATA       : in  std_logic_vector(63 downto 0); -- IB data
      IB_IN_SOP_N      : in  std_logic;                     -- start of packet
      IB_IN_EOP_N      : in  std_logic;                     -- end of packet
      IB_IN_SRC_RDY_N  : in  std_logic;                     -- source ready
      IB_IN_DST_RDY_N  : out std_logic;                     -- destination ready  

      END_OF_ALIGN     : in  std_logic;                     -- end of alignment
      LOCK_READ        : in  std_logic;                     -- no next read can be accepted

      -- Internal Bus OUTPUT interface ----------------------------------------
      IB_OUT_DATA      : out std_logic_vector(63 downto 0); -- IB data
      IB_OUT_SOP_N     : out std_logic;                     -- start of packet
      IB_OUT_EOP_N     : out std_logic;                     -- end of packet
      IB_OUT_SRC_RDY_N : out std_logic;                     -- source ready
      IB_OUT_DST_RDY_N : in  std_logic                      -- destination ready  
   );
end TX_BUF_ALIGN;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  TX Buffer Data Alignment         --
-- ----------------------------------------------------------------------------

architecture tx_buf_align_arch of TX_BUF_ALIGN is

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------
   
   constant T_L2GW : std_logic_vector(3 downto 0) := "0010";
   constant T_G2LR : std_logic_vector(3 downto 0) := "0011";
   constant T_CPL  : std_logic_vector(3 downto 0) := "1101"; 

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   -- FSM types and signals
   type   fsm_states is (S_IDLE, S_DISCARD, S_NOALIGN, S_ALIGN_H2, S_ALIGN_BUFFER,
                         S_ALIGN_DATA, S_ALIGN_DATA_AUX, S_ALIGN_NOALIGN, S_ALIGN_WAIT);
   signal present_state, next_state : fsm_states;

   -- Auxiliary signals 
   signal mpx_data      : std_logic_vector(63 downto 0);
   signal out_sop_n     : std_logic;
   signal out_eop_n     : std_logic;
   signal out_src_rdy_n : std_logic;
   signal in_dst_rdy_n  : std_logic;
   signal align_bit     : std_logic;
   signal trans_type    : std_logic_vector( 3 downto 0);
   signal length        : std_logic_vector(11 downto 0);
   signal addr10        : std_logic_vector( 1 downto 0);
   signal mpx_sel       : std_logic_vector( 1 downto 0);
   signal do_align      : std_logic;
   signal length_one    : std_logic;
   signal bm_result     : std_logic;
   signal data_dly      : std_logic_vector(31 downto 0);
   signal length_even   : std_logic;
   signal reg_length_DW : std_logic_vector(12 downto 0);
   signal mpx_length    : std_logic_vector(12 downto 0);
   signal reg_addr10    : std_logic_vector( 1 downto 0);
   signal reg_length    : std_logic_vector(11 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                              CONTROL FSM                               --
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
   nextstatelogicp : process(present_state,IB_IN_SOP_N,IB_IN_SRC_RDY_N,IB_OUT_DST_RDY_N,trans_type,align_bit,
                             IB_IN_EOP_N,length_even,END_OF_ALIGN,bm_result, LOCK_READ)
   begin
      next_state <= present_state;

      case (present_state) is

         when  S_IDLE => 
            if (LOCK_READ = '0') then
                                                                                                   -- is/is not BM result cpldata (after BM L2GW)         
               if (((IB_IN_SOP_N = '0' and IB_IN_SRC_RDY_N = '0' and IB_OUT_DST_RDY_N = '0') and  not (bm_result = '1' and trans_type = T_CPL))or 
                   ((IB_IN_SOP_N = '0' and IB_IN_SRC_RDY_N = '0'                           ) and      (bm_result = '1' and trans_type = T_CPL)) ) then         
                  -- READ 
                  if (trans_type = T_G2LR) then
                     next_state <= S_NOALIGN;
                  -- WRITE
                  elsif (trans_type = T_L2GW) then
                     if (align_bit = '1') then
                        next_state <= S_ALIGN_H2;
                     else
                        next_state <= S_NOALIGN;
                     end if;
                  -- COMPLETION
                  elsif (trans_type = T_CPL) then
                     if (align_bit = '1') then
                        next_state <= S_ALIGN_WAIT;
                     else
                        next_state <= S_NOALIGN;
                     end if;                  
                  else
                     next_state <= S_DISCARD;
                  end if;
                  
               end if; 
               
            end if;
                       
         -- INVALID TRANSACTION TYPE --
         when  S_DISCARD =>
               if (IB_IN_EOP_N = '0' and IB_IN_SRC_RDY_N = '0') then
                  next_state <= S_IDLE;
               end if;

         -- NO ALIGNMENT --
         when  S_NOALIGN =>
               if (IB_IN_EOP_N = '0' and IB_IN_SRC_RDY_N = '0' and IB_OUT_DST_RDY_N = '0') then
                  next_state <= S_IDLE;
               end if;
            

         -- DATA ALIGNMENT --    
         when  S_ALIGN_WAIT =>
               if (IB_OUT_DST_RDY_N = '0') then
                  next_state <= S_ALIGN_H2;
               end if;
               
         when  S_ALIGN_H2 =>
               if (IB_IN_SRC_RDY_N = '0' and IB_OUT_DST_RDY_N = '0') then
                  next_state <= S_ALIGN_BUFFER;
               end if;
            

         when  S_ALIGN_BUFFER =>
               if (IB_IN_SRC_RDY_N = '0') then
                  if (IB_IN_EOP_N = '0' and IB_OUT_DST_RDY_N = '0') then
                     next_state <= S_IDLE;
                  elsif (IB_IN_EOP_N = '1') then
                     next_state <= S_ALIGN_DATA;
                  end if;
               end if;
                    
         
         when  S_ALIGN_DATA =>                   
                  if (END_OF_ALIGN = '1') then
                     next_state <= S_ALIGN_NOALIGN;                  
                  elsif ((IB_OUT_DST_RDY_N = '0') and IB_IN_EOP_N = '0' and IB_IN_SRC_RDY_N = '0') then                   
                     if (length_even = '1') then
                        next_state <= S_IDLE;
                     else 
                        next_state <= S_ALIGN_DATA_AUX;
                     end if;                                                           
                  end if;

         when  S_ALIGN_DATA_AUX =>
                  if (IB_OUT_DST_RDY_N = '0') then                                 
                     next_state <= S_IDLE;
                  end if;     

         when  S_ALIGN_NOALIGN =>   
                  if ((IB_OUT_DST_RDY_N = '0') and IB_IN_EOP_N = '0' and IB_IN_SRC_RDY_N = '0') then         
                     next_state <= S_IDLE;
                  end if;
                                                                                                                                     
      end case;                                                                                                   
   end process;                                                                                                  
                                                                                                                                        
   -- output logic ------------------------------------------------------------                                       
   outputlogicp : process(present_state,IB_IN_SOP_N,IB_IN_SRC_RDY_N,IB_OUT_DST_RDY_N,trans_type,
                          IB_IN_EOP_N,length_even,END_OF_ALIGN,bm_result, LOCK_READ)                                         
   begin       
      out_sop_n     <= '1';
      out_eop_n     <= '1';
      out_src_rdy_n <= '1';
      in_dst_rdy_n  <= '1';
      do_align      <= '0';
      length_one    <= '0';     

      case (present_state) is   

         when  S_IDLE =>
            if (LOCK_READ = '0') then
            
               in_dst_rdy_n  <= IB_OUT_DST_RDY_N;
                                                                            -- is/is not BM result cpldata (after BM L2GW)         
               if (((IB_IN_SOP_N = '0' and IB_IN_SRC_RDY_N = '0') and  not (bm_result = '1' and trans_type = T_CPL))or 
                   ((IB_IN_SOP_N = '0' and IB_IN_SRC_RDY_N = '0') and      (bm_result = '1' and trans_type = T_CPL)) ) then
                  if (trans_type = T_G2LR or trans_type = T_L2GW or trans_type = T_CPL) then
                     out_sop_n     <= '0';
                     out_src_rdy_n <= '0';                  
                  end if;
               end if;                                                                                             

            end if;
                
         -- INVALID TRANSACTION TYPE --       
         when  S_DISCARD =>
               in_dst_rdy_n  <= '0';

        -- NO ALIGNMENT --
         when  S_NOALIGN =>
               out_sop_n     <= IB_IN_SOP_N;
               out_src_rdy_n <= IB_IN_SRC_RDY_N;
               out_eop_n     <= IB_IN_EOP_N;
               in_dst_rdy_n  <= IB_OUT_DST_RDY_N;               

         -- DATA ALIGNMENT --    
         when S_ALIGN_WAIT =>
               out_sop_n     <= '0';
               out_src_rdy_n <= '0';    
               in_dst_rdy_n  <= IB_OUT_DST_RDY_N;                  
         
         when  S_ALIGN_H2 =>
              out_src_rdy_n <= IB_IN_SRC_RDY_N; 
              in_dst_rdy_n  <= IB_OUT_DST_RDY_N;

         when  S_ALIGN_BUFFER =>                              
               in_dst_rdy_n  <= '0';               
               do_align      <= '1';               
         
               if (IB_IN_SRC_RDY_N = '0' and IB_IN_EOP_N = '0') then
                  length_one    <= '1';
                  out_eop_n     <= '0';
                  out_src_rdy_n <= '0';
                  in_dst_rdy_n  <= IB_OUT_DST_RDY_N;
               end if;
                  
         when  S_ALIGN_DATA =>    
                  do_align      <= '1';                                                         
                  in_dst_rdy_n  <= IB_OUT_DST_RDY_N;                                            
                                                                                                
                  if (END_OF_ALIGN = '1') then                                                  
                     out_src_rdy_n <= '0';                                         
                     in_dst_rdy_n  <= '1';
                  elsif (IB_IN_SRC_RDY_N = '0') then                                                 
                     out_src_rdy_n <= '0';
                        
                     if (IB_OUT_DST_RDY_N = '0') then               
                        in_dst_rdy_n   <= '0';
                        if (IB_IN_EOP_N = '0') then
                           if (length_even = '1') then
                              out_eop_n <= '0';     
                           end if;
                        end if;                        
                     end if;                                                                                                                                
                  end if;

         when  S_ALIGN_DATA_AUX =>
                  out_src_rdy_n <= '0';         
                  out_eop_n     <= '0';
                  do_align      <= '1';
                  in_dst_rdy_n  <= '1';

         when  S_ALIGN_NOALIGN =>
                  out_sop_n     <= IB_IN_SOP_N;
                  out_src_rdy_n <= IB_IN_SRC_RDY_N;
                  out_eop_n     <= IB_IN_EOP_N;
                  in_dst_rdy_n  <= IB_OUT_DST_RDY_N;                               
      
      end case;       
   end process;       

   -- auxiliary logic ---------------------------------------------------------
   reglenaddrp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (IB_IN_SOP_N = '0' and IB_IN_SRC_RDY_N = '0') then
           reg_length <= length; 
           reg_addr10 <= addr10; 
        end if;
     end if;
   end process;     

   mpx_length <= '1'&X"000" when reg_length = 0 else
                 '0'&reg_length; 

   reg_length_DWp: process(mpx_length, reg_addr10)
   begin
      reg_length_DW <= mpx_length + (X"00"&"000"&reg_addr10)  + ('0'&X"003");
   end process;    

   length_even <= not reg_length_DW(2);  

   -- -------------------------------------------------------------------------
   --                           DATA ALIGNMENT LOGIC                         --
   -- -------------------------------------------------------------------------   
   data_dlyp: process(RESET, CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (IB_IN_SRC_RDY_N = '0' and in_dst_rdy_n = '0') then
           data_dly <= IB_IN_DATA(63 downto 32);
        end if;
     end if;
   end process;  

   mpx_sel <= do_align&length_one;

   mpx_datap: process(mpx_sel, IB_IN_DATA, data_dly)
   begin
      case mpx_sel is
         when "00" => mpx_data <= IB_IN_DATA;
         when "10" => mpx_data <= IB_IN_DATA(31 downto 0)&data_dly;
         when "11" => mpx_data <= IB_IN_DATA(31 downto 0)&IB_IN_DATA(63 downto 32);
         when others => mpx_data <= (others => '0');
      end case;
   end process;  

   -- -------------------------------------------------------------------------
   --                             INPUT INTERFACE                            --
   -- -------------------------------------------------------------------------
   align_bit  <= IB_IN_DATA(34);
   trans_type <= IB_IN_DATA(15 downto 12);
   length     <= IB_IN_DATA(11 downto  0);
   addr10     <= IB_IN_DATA(33 downto 32);
   bm_result  <= IB_IN_DATA(23);

   -- -------------------------------------------------------------------------
   --                            OUTPUT INTERFACE                            --
   -- -------------------------------------------------------------------------

   -- Internal Bus INPUT interface --
   IB_IN_DST_RDY_N  <= in_dst_rdy_n; 

   -- Internal Bus OUTPUT interface -- 
   IB_OUT_DATA      <= mpx_data;
   IB_OUT_SOP_N     <= out_sop_n;
   IB_OUT_EOP_N     <= out_eop_n;
   IB_OUT_SRC_RDY_N <= out_src_rdy_n;
      
end tx_buf_align_arch;

                      

