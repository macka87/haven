--
-- up_fsm.vhd : IB Transformer Up FSM
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
use work.ib_transformer_pkg.all;

-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- IB Transformer Up FSM              -- 
-- ----------------------------------------------------------------------------

entity IB_TRANSFORMER_UP_FSM is 
   generic(
      -- Input Data Width (1-64)
      IN_DATA_WIDTH   : integer :=  8;
      -- Output Data Width (2-128)
      OUT_DATA_WIDTH  : integer := 64      
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  
 
      -- IN IB interface ------------------------------------------------------
      IN_SOF_N      : in  std_logic;
      IN_EOF_N      : in  std_logic;
      IN_SRC_RDY_N  : in  std_logic;
      IN_DST_RDY_N  : out std_logic;

      -- OUT IB interface -----------------------------------------------------
      OUT_SOF_N     : out std_logic;
      OUT_EOF_N     : out std_logic;
      OUT_SRC_RDY_N : out std_logic;
      OUT_DST_RDY_N : in  std_logic;      

      -- Control interface ----------------------------------------------------
      CNT_PARTS_RST : out std_logic;  
      CNT_PARTS_CE  : out std_logic;  
      CNT_PARTS_WE  : out std_logic;  
      CNT_PARTS     : in  std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
      PAYLOAD_FLAG  : in  std_logic; 
      HEADER_LAST   : in  std_logic
   );
end IB_TRANSFORMER_UP_FSM;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION  --  IB Transformer Up FSM          --
-- ----------------------------------------------------------------------------

architecture ib_transformer_up_fsm_arch of IB_TRANSFORMER_UP_FSM is

   constant ONES : std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0) := (others => '1'); 

   type   fsm_states is (S_SOF, S_HEADER, S_DATA, S_DATA_LAST);
   signal present_state, next_state : fsm_states; 
   
begin

   -- -------------------------------------------------------------------------                                                         
   --                                 UP FSM                                 --                                                         
   -- -------------------------------------------------------------------------                                                     
                                                                                                                                    
   -- synchronize logic -------------------------------------------------------      
   synchlogp : process(CLK)                                                          
   begin                                                                             
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then                                                                                           
            present_state <= S_SOF; 
         else
            present_state <= next_state;
         end if;
      end if;                                                                                                  
   end process;                                                                                                

   -- next state logic --------------------------------------------------------                                                                                           
   nextstatelogicp : process(present_state, IN_SOF_N, IN_EOF_N, IN_SRC_RDY_N, OUT_DST_RDY_N,
                                            CNT_PARTS, PAYLOAD_FLAG, HEADER_LAST) 
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               

         -- S_SOF -----------------------------------------
         when  S_SOF =>
            if (CNT_PARTS = ONES and IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0') then
               if (OUT_DATA_WIDTH = 128) then
                  if (PAYLOAD_FLAG = '1') then
                     next_state <= S_DATA;
                  else
                     next_state <= S_SOF;
                  end if;
               else                 
                  next_state <= S_HEADER;
               end if;
            end if;

         -- S_HEADER --------------------------------------
         when  S_HEADER =>                                                              
            if (HEADER_LAST = '1' and OUT_DST_RDY_N = '0') then
               if (PAYLOAD_FLAG = '1') then
                  next_state <= S_DATA;
               else
                  next_state <= S_SOF;
               end if;
            end if;
                                                                                                                   
         -- S_DATA ----------------------------------------
         when  S_DATA =>
            if (IN_EOF_N = '0') then
               if (CNT_PARTS = ONES) then
                  if (OUT_DST_RDY_N = '0') then
                     next_state <= S_SOF;
                  end if;
               else
                  next_state <= S_DATA_LAST;
               end if;
            end if;   

         -- S_DATA_LAST -----------------------------------
         when  S_DATA_LAST =>
            if (OUT_DST_RDY_N = '0') then
               next_state <= S_SOF;
            end if;         
        
      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state, IN_SOF_N, IN_EOF_N, IN_SRC_RDY_N, OUT_DST_RDY_N,
                                         CNT_PARTS, PAYLOAD_FLAG, HEADER_LAST)
   begin 
      IN_DST_RDY_N   <= '1';
      OUT_SOF_N      <= '1';
      OUT_EOF_N      <= '1';
      OUT_SRC_RDY_N  <= '1';
      CNT_PARTS_RST  <= '0';
      CNT_PARTS_CE   <= '0';
      CNT_PARTS_WE   <= '0';
      
      case (present_state) is 
 
         -- S_SOF -----------------------------------------
         when  S_SOF =>

            if (CNT_PARTS = ONES) then
               if (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0') then
                  IN_DST_RDY_N   <= '0';
                  OUT_SOF_N      <= '0';
                  OUT_SRC_RDY_N  <= '0';               

                  if (OUT_DATA_WIDTH = 128) then
                     if (PAYLOAD_FLAG = '1') then
                        CNT_PARTS_WE   <= '1';                        
                     else
                        CNT_PARTS_RST  <= '1';
                        OUT_EOF_N      <= '0';
                     end if;
                  else
                     CNT_PARTS_CE   <= '1';
                  end if;
               end if;
            else
               IN_DST_RDY_N   <= '0';
               CNT_PARTS_CE   <= not IN_SRC_RDY_N;
            end if;

         -- S_HEADER --------------------------------------
         when  S_HEADER =>   

            if (CNT_PARTS = ONES) then
               if (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0') then
                  IN_DST_RDY_N   <= '0';
                  OUT_SRC_RDY_N  <= '0';      

                  if (HEADER_LAST = '1') then
                     if (PAYLOAD_FLAG = '1') then
                        CNT_PARTS_WE   <= '1';                        
                     else
                        CNT_PARTS_RST  <= '1';
                        OUT_EOF_N      <= '0';
                     end if;
                  else
                     CNT_PARTS_CE   <= '1';                                   
                  end if;                                                     
                                                                              
               end if;                                                        
            else                                                              
               IN_DST_RDY_N   <= '0';                                         
               CNT_PARTS_CE   <= not IN_SRC_RDY_N;                            
            end if;
                                                                                                                  
         -- S_DATA ----------------------------------------
         when  S_DATA =>

            if (IN_EOF_N = '0') then
               if (CNT_PARTS = ONES) then
                  if (OUT_DST_RDY_N = '0') then
                     IN_DST_RDY_N   <= '0';
                     OUT_SRC_RDY_N  <= '0';      
                     CNT_PARTS_RST  <= '1';
                     OUT_EOF_N      <= '0';                     
                  end if;
               else
                  IN_DST_RDY_N   <= '0';
                  CNT_PARTS_RST  <= '1';
               end if;
            else
               if (CNT_PARTS = ONES) then
                  if (IN_SRC_RDY_N = '0' and OUT_DST_RDY_N = '0') then                          
                     IN_DST_RDY_N   <= '0';                                                     
                     OUT_SRC_RDY_N  <= '0';                                                     
                     CNT_PARTS_CE   <= '1';                                                     
                  end if;                                                                       
               else                                                                             
                  IN_DST_RDY_N   <= '0';                                                        
                  CNT_PARTS_CE   <= not IN_SRC_RDY_N;
               end if;
            end if;    

         -- S_DATA_LAST -----------------------------------
         when  S_DATA_LAST =>
         
            if (OUT_DST_RDY_N = '0') then
               IN_DST_RDY_N   <= '0';
               OUT_EOF_N      <= '0';
               OUT_SRC_RDY_N  <= '0';
               CNT_PARTS_CE   <= not IN_SRC_RDY_N;
            end if;                     

      end case;                                                                                                   
   end process;                                                                                                   
   
end ib_transformer_up_fsm_arch;



