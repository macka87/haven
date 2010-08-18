-- align_unit_fake.vhd : Alignment Fake Unit (only generates SOF & EOF)
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

use work.math_pack.all; 

-- ----------------------------------------------------------------------------
--    ENTITY DECLARATION -- Alignment Fake Unit (only generates SOF & EOF)   -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_READ_CTRL_ALIGN_UNIT_FAKE is 
   generic(
      DATA_WIDTH    : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;  
      RESET         : in std_logic;  

      -- Control interface ----------------------------------------------------
      COUNT         : in  std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);
      NEXT_TRANS    : out std_logic;  

      -- Input interface ------------------------------------------------------
      IN_DATA       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SRC_RDY    : in  std_logic;
      IN_DST_RDY    : out std_logic;      

      -- Output interface -----------------------------------------------------
      OUT_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      OUT_SOF       : out std_logic;
      OUT_EOF       : out std_logic;      
      OUT_SRC_RDY   : out std_logic;      
      OUT_DST_RDY   : in  std_logic
   );
end IB_ENDPOINT_READ_CTRL_ALIGN_UNIT_FAKE;

-- ----------------------------------------------------------------------------
--  ARCHITECTURE DECLARATION -- Alignment Fake Unit (only generates SOF&EOF) --
-- ----------------------------------------------------------------------------

architecture align_unit_fake_arch of IB_ENDPOINT_READ_CTRL_ALIGN_UNIT_FAKE is

   type   fsm_states is (S_IDLE, S_TRANSFER);
   signal present_state, next_state : fsm_states; 

   signal cnt_data_ce : std_logic;
   signal cnt_data_we : std_logic;
   signal cnt_data    : std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);

begin

   -- -------------------------------------------------------------------------                                                         
   --                              DATA COUNTER                              --                                                         
   -- -------------------------------------------------------------------------                                                     

   cnt_datap: process (CLK) 
   begin
      if (CLK = '1' and CLK'event) then
         if (RESET = '1') then 
            cnt_data <= (others => '0');
         elsif (cnt_data_ce = '1') then  
            cnt_data <= cnt_data - 1;            
         elsif (cnt_data_we = '1') then  
            cnt_data <= COUNT;
         end if;
      end if;
   end process; 

   -- -------------------------------------------------------------------------                                                         
   --                              CONTROL FSM                               --                                                         
   -- -------------------------------------------------------------------------                                                     
                                                                                                                                    
   -- synchronize logic -------------------------------------------------------                     
   synchlogp : process(CLK)
   begin 
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then 
            present_state <= S_IDLE; 
         else 
            present_state <= next_state;
         end if;
      end if;
   end process;                                                                                                

   -- next state logic --------------------------------------------------------                                                                                           
   nextstatelogicp : process(present_state, IN_SRC_RDY, OUT_DST_RDY, cnt_data) 
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               

         -- S_IDLE ----------------------------------------
         when  S_IDLE =>
            if (IN_SRC_RDY = '1' and OUT_DST_RDY = '1' and cnt_data /= 1) then
               next_state <= S_TRANSFER;
            end if;

         -- S_TRANSFER -------------------------------------
         when  S_TRANSFER =>
            if (IN_SRC_RDY = '1' and OUT_DST_RDY = '1' and cnt_data = 1) then
               next_state <= S_IDLE;
            end if;         

      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state, IN_SRC_RDY, OUT_DST_RDY, cnt_data, IN_DATA)
   begin              
      OUT_SOF     <= '0';
      OUT_EOF     <= '0';
      
      NEXT_TRANS  <= '0';
      
      cnt_data_we <= '0';
      cnt_data_ce <= '0';
      
      OUT_SRC_RDY <= IN_SRC_RDY;
      IN_DST_RDY  <= OUT_DST_RDY;
      OUT_DATA    <= IN_DATA;  
      
      case (present_state) is 
 
         -- S_IDLE --------------------------------------
         when  S_IDLE =>
            cnt_data_we <= '1';

            if (IN_SRC_RDY = '1') then
               OUT_SOF  <= '1';
               
               if (cnt_data = 1) then
                  OUT_EOF    <= '1';
                  NEXT_TRANS <= OUT_DST_RDY;
               end if;

               if (OUT_DST_RDY = '1') then
                  cnt_data_ce <= '1';
               end if;
            end if;         

         -- S_TRANSFER -------------------------------------
         when  S_TRANSFER =>
            
            if (IN_SRC_RDY = '1') then
               if (cnt_data = 1) then
                  OUT_EOF    <= '1';
                  NEXT_TRANS <= OUT_DST_RDY;
               end if;

               if (OUT_DST_RDY = '1') then
                  cnt_data_ce <= '1';
               end if;         
            end if;
         
      end case;                                                                                                   
   end process;

end align_unit_fake_arch;



