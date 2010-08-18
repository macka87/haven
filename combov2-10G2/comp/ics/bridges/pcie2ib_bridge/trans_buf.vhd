--
-- trans_buf.vhd : 'PCIe Endpoint Block to TLP DEC/GEN' Transformation buffer
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
--                 ENTITY DECLARATION -- Transformation Buffer               -- 
-- ----------------------------------------------------------------------------

entity TRANS_BUF is 
   generic(
      BAR_HIT_MASK     : std_logic_vector(6 downto 0)  := "1111111";   -- Base Address Register hit mask
      -- BAR base addresses
      BAR0_BASE        : std_logic_vector(31 downto 0) := X"01000000"; -- BAR0 base address for PCIE->IB transalation
      BAR1_BASE        : std_logic_vector(31 downto 0) := X"02000000"; -- BAR1 base address for PCIE->IB transalation
      BAR2_BASE        : std_logic_vector(31 downto 0) := X"03000000"; -- BAR2 base address for PCIE->IB transalation
      BAR3_BASE        : std_logic_vector(31 downto 0) := X"04000000"; -- BAR3 base address for PCIE->IB transalation
      BAR4_BASE        : std_logic_vector(31 downto 0) := X"06000000"; -- BAR4 base address for PCIE->IB transalation
      BAR5_BASE        : std_logic_vector(31 downto 0) := X"08000000"; -- BAR5 base address for PCIE->IB transalation       
      BAR6_BASE        : std_logic_vector(31 downto 0) := X"0A000000"; -- ROM  base address for PCIE->IB transalation
      -- BAR base addresses masks
      BAR0_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR0 mask for PCIE->IB transalation
      BAR1_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR1 mask for PCIE->IB transalation
      BAR2_MASK        : std_logic_vector(31 downto 0) := X"00FFFFFF"; -- BAR2 mask for PCIE->IB transalation
      BAR3_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR3 mask for PCIE->IB transalation
      BAR4_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR4 mask for PCIE->IB transalation
      BAR5_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"; -- BAR5 mask for PCIE->IB transalation       
      BAR6_MASK        : std_logic_vector(31 downto 0) := X"01FFFFFF"  -- ROM  mask for PCIE->IB transalation                  
   ); 
   port (
      -- clock & reset --------------------------------------------------------
      CLK              : in std_logic;  -- FPGA clock
      RESET            : in std_logic;  -- Reset active high

      -- PCI Express Transaction Layer interface ------------------------------
      -- RX link --
      PCIERX_SOF_N     : in std_logic;                      -- signals the start of a packet
      PCIERX_EOF_N     : in std_logic;                      -- signals the end of a packet
             
      PCIERX_DATA      : in std_logic_vector(63 downto 0);  -- packet data to be transmitted
      PCIERX_REM_N     : in std_logic_vector( 7 downto 0);  -- packet data validity (legal values: 00000000/00001111)
             
      PCIERX_SRC_RDY_N : in std_logic;                      -- source ready
      PCIERX_DST_RDY_N : out std_logic;                     -- destination ready 
                                                                                                                                         
      PCIERX_SRC_DSC_N : in std_logic;                      -- source discontinue, asserted when the physical link is going into reset.
      PCIERX_ERR_FWD_N : in std_logic;                      -- error forward, marks the packet in progress as error poisoned
      PCIERX_NP_OK_N   : out std_logic;                     -- Non-Posted OK, ready to accept a Non-Posted Request packet
                                                                                                                                         
      PCIERX_BAR_HIT_N : in std_logic_vector( 6 downto 0);  -- Indicates BAR(s) targeted by the current receive transaction      
                                                                                                                                         
      PCIERX_FC_PH_AV  : in std_logic_vector( 7 downto 0);  -- The number of Posted Header FC credits available to the remote link partner.
      PCIERX_FC_PD_AV  : in std_logic_vector(11 downto 0);  -- The number of Posted Data FC credits available to the remote link partner
      PCIERX_FC_NPH_AV : in std_logic_vector( 7 downto 0);  -- Number of Non-Posted Header FC credits available to the remote link partner
      PCIERX_FC_NPD_AV : in std_logic_vector(11 downto 0);  -- Number of Non-Posted Data FC credits available to the remote link partner

      -- TX link --
      PCIETX_SOF_N     : out std_logic;                     -- signals the start of a packet
      PCIETX_EOF_N     : out std_logic;                     -- signals the end of a packet
             
      PCIETX_DATA      : out std_logic_vector(63 downto 0); -- packet data to be transmitted
      PCIETX_REM_N     : out std_logic_vector( 7 downto 0); -- packet data validity (legal values: 00000000/00001111)
             
      PCIETX_SRC_RDY_N : out std_logic;                     -- source ready
      PCIETX_DST_RDY_N : in std_logic;                      -- destination ready 
                                                                                                                                                                 
      PCIETX_SRC_DSC_N : out std_logic;                     -- source discontinue, may be asserted any time starting on the first cycle after SOF to EOF, inclusive
      PCIETX_DST_DCS_N : in std_logic;                      -- destination discontinue: Asserted when the physical link is going into reset.
                                                                                                                                                                 
      PCIETX_BUF_AV    : in std_logic_vector( 2 downto 0);  -- Indicates transmit buffer availability in the core (0:Non-Posted,1:Posted,2:Completion)

      -- TLP generator/decoder interface --------------------------------------
      -- Decoder --
      TLPRX_REQ            : out std_logic;                    -- TLP data ready - receive requested
      TLPRX_ACK            : in  std_logic;                    -- TLP data acknowledge - application acceppts data
      TLPRX_WAIT           : in  std_logic;                    -- Pause TLP data
      TLPRX_READY          : in  std_logic;                    -- TLP decoder ready
      TLPRX_IDLE           : out std_logic;                    -- TransBuffer is idle
      TLPRX_CORE           : out std_logic;                    -- PCIe CORE (CAST=0/XILINX=1)      
      TLPRX_READBACK       : out std_logic;                    -- Read-Back Write detected      
      TLPRX_BARBASE        : out std_logic_vector(31 downto 0);-- Bar base address for IB transaction translation
      TLPRX_BARMASK        : out std_logic_vector(31 downto 0);-- Bar base address mask for IB transaction translation      
      TLPRX_FULL           :  in std_logic;                    -- Local Read Buffer full flag -> block next read

      TLPRX_DATA           : out std_logic_vector(63 downto 0); -- TLP receive data
      TLPRX_DWE            : out std_logic_vector(1 downto 0);  -- TLP transmit data DW enable           

      -- Generator --
      TLPTX_REQ            : in  std_logic;                     -- Request TLP transmission
      TLPTX_ACK            : out  std_logic;                     -- TLM ready to accept TLP
      TLPTX_WAIT           : out  std_logic;                     -- Pause TLP data
                           
      TLPTX_DATA           : in  std_logic_vector(63 downto 0); -- TLP transmit data
      TLPTX_DWE            : in  std_logic_vector(1 downto 0)   -- TLP transmit data DW enable   
      
   );
end TRANS_BUF;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  Transformation Buffer            --
-- ----------------------------------------------------------------------------

architecture trans_buf_arch of TRANS_BUF is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   -- PCIE ENDPOINT BLOCK RX INTERFACE --> TLP DECODER INTERFACE signals ------
   type   fsm_states is (S_IDLE, S_REQ, S_RECEIVE, S_RECEIVE_AUX, S_EOF, S_DISCARD);
   signal present_state, next_state : fsm_states; 

   signal pcierx_data_reg  : std_logic_vector(63 downto 0); 
   signal pcierx_rem_n_reg : std_logic_vector( 7 downto 0); 
   signal pcierx_rem_n_valid : std_logic;
   signal reg_write        : std_logic; 
   signal tlprx_req_rst    : std_logic; 
   signal tlprx_req_en     : std_logic; 
   signal bar_hit_result   : std_logic;
   signal read_back        : std_logic;
   signal read_back_en     : std_logic;
   signal read_back_reg    : std_logic := '0';
   signal dwe_11           : std_logic;
   signal bar_base_reg     : std_logic_vector(31 downto 0); 
   signal bar_mask_reg     : std_logic_vector(31 downto 0);   
   signal bar_base         : std_logic_vector(31 downto 0); 
   signal bar_mask         : std_logic_vector(31 downto 0);   
   signal bar_base_en      : std_logic;
   signal supported        : std_logic;
   signal np_ok_n_reg_en   : std_logic;
   signal np_ok_n_reg      : std_logic;
   
   -- PCIE ENDPOINT BLOCK TX INTERFACE <-- TLP GENERATOR INTERFACE signals ----
   type   txfsm_states is (TX_S_IDLE, TX_S_SOF, TX_S_TRANSMIT);
   signal tx_present_state, tx_next_state : txfsm_states;    

   -- -------------------------------------------------------------------------
   --                           Constant declaration                         --
   -- -------------------------------------------------------------------------
 
   constant TLPFMT_3DWH_ND : std_logic_vector(1 downto 0) := "00";     
   constant TLPFMT_4DWH_ND : std_logic_vector(1 downto 0) := "01";     
   constant TLPFMT_3DWH_WD : std_logic_vector(1 downto 0) := "10";     
   constant TLPFMT_4DWH_WD : std_logic_vector(1 downto 0) := "11";     
 
   constant TLPTYPE_MEM    : std_logic_vector(4 downto 0) := "00000";
   constant TLPTYPE_CPL    : std_logic_vector(4 downto 0) := "01010";

   constant TLPCMD_MRD32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MRD64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_ND & TLPTYPE_MEM;
   constant TLPCMD_MWR32   : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_MWR64   : std_logic_vector(6 downto 0) := TLPFMT_4DWH_WD & TLPTYPE_MEM;
   constant TLPCMD_CPLD    : std_logic_vector(6 downto 0) := TLPFMT_3DWH_WD & TLPTYPE_CPL;

begin

   -- -------------------------------------------------------------------------
   --        PCIE ENDPOINT BLOCK RX INTERFACE --> TLP DECODER INTERFACE      --
   -- ------------------------------------------------------------------------- 
                                                                                                               
   -- synchronize logic                                                                                        
   synchlogp : process(RESET, CLK)                                                                              
   begin                                                                                                        
      if (RESET = '1') then                                                                                       
         present_state <= S_IDLE;                                                                              
      elsif (CLK'event and CLK = '1') then                                                                     
         present_state <= next_state;                                                                           
      end if;                                                                                                  
   end process;                                                                                                

   -- next state logic                                                                                            
   nextstatelogicp : process(present_state,TLPRX_READY, PCIERX_SOF_N, PCIERX_SRC_RDY_N, bar_hit_result, 
                             PCIERX_EOF_N, TLPRX_ACK,TLPRX_WAIT, supported)    
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               
                                                                                                                  
         when  S_IDLE =>                                                                                          
                  if (PCIERX_SOF_N = '0' and PCIERX_SRC_RDY_N = '0' and bar_hit_result = '1') then
                     if (supported = '0') then
                       next_state <= S_DISCARD;                     
                     elsif (TLPRX_READY = '1') then
                       next_state <= S_REQ;
                     end if;
                  end if;

         when  S_REQ =>                    
                  next_state <= S_RECEIVE;                 
 
         when  S_RECEIVE =>   
                  if    (PCIERX_EOF_N = '0' and PCIERX_SRC_RDY_N = '0' and TLPRX_ACK = '1' and TLPRX_WAIT = '0') then
                     next_state <= S_EOF;
                  elsif (PCIERX_SRC_RDY_N = '1' and TLPRX_ACK = '1' and TLPRX_WAIT = '0') then
                     next_state <= S_RECEIVE_AUX;
                  end if;         

         when  S_RECEIVE_AUX =>  
                  if    (PCIERX_EOF_N = '0' and PCIERX_SRC_RDY_N = '0') then
                     next_state <= S_EOF;
                  elsif (PCIERX_SRC_RDY_N = '0') then
                     next_state <= S_RECEIVE;
                  end if;                           

         when  S_EOF =>   
                  if (TLPRX_ACK = '1' and TLPRX_WAIT = '0') then
                     next_state <= S_IDLE;
                  end if;                        

         when  S_DISCARD =>   
                  if (PCIERX_EOF_N = '0' and PCIERX_SRC_RDY_N = '0') then
                     next_state <= S_IDLE;
                  end if;                                                                              
      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic                                                                                                 
   outputlogicp : process(present_state,TLPRX_READY, PCIERX_SOF_N, PCIERX_SRC_RDY_N, bar_hit_result, 
                          TLPRX_ACK,TLPRX_WAIT, supported, TLPRX_FULL)
   begin                                                                                                                 
        
     reg_write          <= '0';
     pcierx_rem_n_valid <= '0';     
     dwe_11             <= '0';          
     read_back_en       <= '0';
     bar_base_en        <= '0';
        
     TLPRX_CORE       <= '1';
     TLPRX_IDLE       <= '0';
     tlprx_req_en     <= '0';
                                                                                                                                          
     np_ok_n_reg_en   <= '0';
     PCIERX_DST_RDY_N <= '1';
                                                                                                                                        
      case (present_state) is                                                                                     
                                                                                                                   
         when  S_IDLE =>                                                                                          
                  TLPRX_IDLE       <= '1';
                  
                  if (TLPRX_READY = '1') then
                     PCIERX_DST_RDY_N <= '0';
                  end if;

                  if (TLPRX_FULL = '1') then
                     np_ok_n_reg_en <= '1';
                  end if;
                  
                  if (PCIERX_SOF_N = '0' and PCIERX_SRC_RDY_N = '0' and bar_hit_result = '1') then
                     if (supported = '0') then
                       PCIERX_DST_RDY_N <= '0';           
                     elsif (TLPRX_READY = '1') then                                         
                       reg_write        <= '1';
                       tlprx_req_en     <= '1';
                       read_back_en     <= '1';
                       bar_base_en      <= '1';
                     end if;
                  end if;         

         when  S_REQ =>
                  dwe_11 <= '1';

         when  S_RECEIVE =>  
                  dwe_11 <= '1';

                  if (PCIERX_SRC_RDY_N = '0') then
                     tlprx_req_en  <= '1';
                  end if;                                                                
                     
                  if (TLPRX_ACK = '1' and TLPRX_WAIT = '0') then
                     PCIERX_DST_RDY_N <= '0';                     
                  
                     -- if (PCIERX_SRC_RDY_N = '0') then
                     reg_write      <= '1';
                     -- end if;

                  end if;

         when  S_RECEIVE_AUX =>  
                  PCIERX_DST_RDY_N <= '0';
                  reg_write        <= '1';
                  
                  if  (PCIERX_SRC_RDY_N = '0') then
                     tlprx_req_en  <= '1';
                  end if;     

         when  S_EOF =>   
                  if (TLPRX_ACK = '1' and TLPRX_WAIT = '0') then
                     pcierx_rem_n_valid <= '1';
                  end if;     

         when  S_DISCARD =>   
                  PCIERX_DST_RDY_N <= '0';
         
      end case;                                                                                                    
   end process;                                                                                                                         

   -- auxiliary TLPRX_REQ logic
   tlprx_req_rst <= (not tlprx_req_en) and TLPRX_ACK and (not TLPRX_WAIT);
   tlprx_reqp: process(RESET, CLK, tlprx_req_rst)
   begin
     if (RESET = '1' or tlprx_req_rst = '1') then
        TLPRX_REQ  <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (tlprx_req_en = '1') then
           TLPRX_REQ  <= '1';
        end if;
     end if;
   end process;      

   -- auxiliary TLP_BAR_HIT logic
   BARHIT_PROC: process(PCIERX_BAR_HIT_N)
   variable hit1 : std_logic;
   --variable hit2 : std_logic;
   begin
      hit1 := '0';
      --hit2 := '0';
      for i in 0 to PCIERX_BAR_HIT_N'high loop
         if (PCIERX_BAR_HIT_N(i) = '0') and (BAR_HIT_MASK(i) = '1') then
            hit1 := '1';
         end if;
         --if (PCIERX_BAR_HIT_N(i) = '0') and (BAR_HIT_MASK2(i) = '1') then
         --   hit2 := '1';
         --end if;
      end loop;
      bar_hit_result <= hit1; --or hit2;
      --read_back <= '0';--hit2;
   end process; 

   read_back_regp: process(RESET, CLK)
   begin
     if (RESET = '1') then
        read_back_reg  <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (read_back_en = '1') then
           read_back_reg  <= read_back;
        end if;
     end if;
   end process;         

   TLPRX_READBACK <= '0'; -- read_back_reg;   

   -- BAR decoding and logic
   bar_base_maskp: process(CLK)
   begin
     if    (PCIERX_BAR_HIT_N(0) = '0') then
        bar_base  <= BAR0_BASE;
        bar_mask  <= BAR0_MASK;        
     elsif (PCIERX_BAR_HIT_N(1) = '0') then
        bar_base  <= BAR1_BASE;     
        bar_mask  <= BAR1_MASK;        
     elsif (PCIERX_BAR_HIT_N(2) = '0') then
        bar_base  <= BAR2_BASE;     
        bar_mask  <= BAR2_MASK;        
     elsif (PCIERX_BAR_HIT_N(3) = '0') then
        bar_base  <= BAR3_BASE;     
        bar_mask  <= BAR3_MASK;        
     elsif (PCIERX_BAR_HIT_N(4) = '0') then
        bar_base  <= BAR4_BASE;     
        bar_mask  <= BAR4_MASK;        
     elsif (PCIERX_BAR_HIT_N(5) = '0') then
        bar_base  <= BAR5_BASE;                     
        bar_mask  <= BAR5_MASK;        
     else
        bar_base  <= BAR6_BASE;
        bar_mask  <= BAR6_MASK;        
     end if;
   end process;      
   
   bar_base_mask_regp: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (bar_base_en = '1') then
           bar_base_reg  <= bar_base;
           bar_mask_reg  <= bar_mask;           
        end if;
     end if;
   end process;        

   TLPRX_BARBASE <= bar_base_reg;
   TLPRX_BARMASK <= bar_mask_reg;   

   -- data logic 
   pcierx_datap: process(CLK)
   begin
     if (CLK'event AND CLK = '1') then
        if (reg_write  = '1') then
           pcierx_data_reg  <= PCIERX_DATA;
           pcierx_rem_n_reg <= PCIERX_REM_N;           
        end if;
     end if;
   end process;   

   TLPRX_DATA <= pcierx_data_reg;

   TLPRX_DWE  <= (not pcierx_rem_n_reg(4))&(not pcierx_rem_n_reg(0)) when pcierx_rem_n_valid = '1' else
                 "11" when dwe_11 = '1' else
                 "00";
   
   -- (un)supported transaction decoder
   supportedp: process(CLK, PCIERX_DATA(62 downto 56))
   begin
      supported <= '0';

      case PCIERX_DATA(62 downto 56) is -- 00 11100
         when TLPCMD_MRD32 => supported <= '1';          
         when TLPCMD_MRD64 => supported <= '1';                   
         when TLPCMD_MWR32 => supported <= '1';                            
         when TLPCMD_MWR64 => supported <= '1';                            
         when TLPCMD_CPLD  => supported <= '1';
         when others       => supported <= '0';
      end case;
   end process;

   -- PCIERX_NP_OK_N register and logic
   np_ok_n_regp: process(RESET, CLK, TLPRX_FULL)
   begin
     if (RESET = '1' or TLPRX_FULL = '0') then
        np_ok_n_reg  <= '0';
     elsif (CLK'event AND CLK = '1') then
        if (np_ok_n_reg_en = '1') then
           np_ok_n_reg  <= '1';
        end if;
     end if;
   end process;         
  
  PCIERX_NP_OK_N <= TLPRX_FULL;--np_ok_n_reg_en or np_ok_n_reg;
   
   -- -------------------------------------------------------------------------
   --       PCIE ENDPOINT BLOCK TX INTERFACE <-- TLP GENERATOR INTERFACE     --
   -- -------------------------------------------------------------------------   

   -- synchronize logic
   txsynchlogp : process(RESET, CLK)
   begin
      if (RESET = '1') then
         tx_present_state <= TX_S_IDLE;
      elsif (CLK'event and CLK = '1') then
         tx_present_state <= tx_next_state;
      end if;
   end process;   

   -- next state logic
   txnextstatelogicp : process(tx_present_state,TLPTX_REQ,PCIETX_DST_RDY_N)
   begin
      tx_next_state <= tx_present_state;

      case (tx_present_state) is

         when  TX_S_IDLE => 
            if (TLPTX_REQ = '1') then                                                                             
               tx_next_state <= TX_S_SOF;                                                                        
            end if;                                                                                             
                                                                                                                                       
         when  TX_S_SOF =>                                                                                        
            if (PCIETX_DST_RDY_N = '0') then                                                                     
               tx_next_state <= TX_S_TRANSMIT;
            end if;         
                                                                                                                  
         when  TX_S_TRANSMIT =>                                                                                   
            if (TLPTX_REQ = '0' and PCIETX_DST_RDY_N = '0') then                                                         
               tx_next_state <= TX_S_IDLE;                                                                        
            end if;                                                                                               
                                                                                                                         
      end case;                                                                                                   
   end process;                                                                                                  
                                                                                                                                        
   -- output logic                                                                                                
   txoutputlogicp : process(tx_present_state,PCIETX_DST_RDY_N, TLPTX_REQ)                                         
   begin                                                                                                                                
                                                                             
      PCIETX_SOF_N     <= '1';
      PCIETX_EOF_N     <= '1';      
      PCIETX_SRC_RDY_N <= '1';
      PCIETX_SRC_DSC_N <= '1';                            
      
      TLPTX_ACK        <= '0';
      TLPTX_WAIT       <= '0';      

      case (tx_present_state) is   

         when  TX_S_IDLE => 

         when  TX_S_SOF =>
            PCIETX_SOF_N     <= '0';
            PCIETX_SRC_RDY_N <= '0';

            if (PCIETX_DST_RDY_N = '0') then
               TLPTX_ACK <= '1';
            end if;                     

         when  TX_S_TRANSMIT =>             
            TLPTX_ACK  <= '1';         
            TLPTX_WAIT <= PCIETX_DST_RDY_N;
            
            PCIETX_SRC_RDY_N <= '0';
               
            if (TLPTX_REQ = '0') then
               PCIETX_EOF_N <= '0';
            end if;                                        
      
      end case;       
   end process;       

   -- data logic
   PCIETX_DATA      <= TLPTX_DATA;
   PCIETX_REM_N     <= (7 downto 4 => not TLPTX_DWE(1))&(3 downto 0 => not TLPTX_DWE(0));
   
   ----------------------------------------------------------------------------
      
end trans_buf_arch;

                      

