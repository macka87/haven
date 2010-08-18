--
-- down_fsm.vhd : IB Endpoint Down FSM
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
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--              ENTITY DECLARATION -- IB Endpoint Down Buffer FSM            -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_DOWN_FSM is 
   generic (
      -- Data Width (8-128)
      DATA_WIDTH   : integer:= 64
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  
 
      -- IB interface ---------------------------------------------------------
      IB_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);      
      IB_SOF_N     : in  std_logic;
      IB_EOF_N     : in  std_logic;
      IB_SRC_RDY_N : in  std_logic;
      IB_DST_RDY_N : out std_logic;

      IB_REQ       : in  std_logic;
      IB_DROP      : in  std_logic;
      IB_ACK       : out std_logic; 
      
      -- RD interface ---------------------------------------------------------
      RD_SOF_N     : out std_logic;
      RD_EOF_N     : out std_logic;
      RD_SRC_RDY_N : out std_logic;
      RD_DST_RDY_N : in  std_logic;

      -- WR interface ---------------------------------------------------------
      WR_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);      
      WR_SOF_N     : out std_logic;
      WR_EOF_N     : out std_logic;
      WR_SRC_RDY_N : out std_logic;
      WR_DST_RDY_N : in  std_logic      
   );
end IB_ENDPOINT_DOWN_FSM;

-- ----------------------------------------------------------------------------
--           ARCHITECTURE DECLARATION  --  IB Endpoint Down Buffer FSM       --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_down_fsm_arch of IB_ENDPOINT_DOWN_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_ARBITER, S_READ, S_WRITE, S_DROP);
   signal present_state, next_state : fsm_states; 
   
begin

   -- -------------------------------------------------------------------------                                                         
   --                                DOWN FSM                                --                                                         
   -- -------------------------------------------------------------------------                                                     
                                                                                                                                    
   -- synchronize logic -------------------------------------------------------                                                                                         
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

   -- next state logic --------------------------------------------------------                                                                                           
   nextstatelogicp : process(present_state, IB_DATA, IB_SOF_N, IB_EOF_N, IB_SRC_RDY_N, IB_REQ, IB_DROP, RD_DST_RDY_N, WR_DST_RDY_N)    
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               

         -- S_ARBITER ---------------------------------------------------------
         when  S_ARBITER =>
            if (IB_REQ = '1' and IB_SOF_N = '0') then            
               if (IB_EOF_N = '1') then
                  if (IB_DATA(C_IB_TYPE_DATA) = '0' and RD_DST_RDY_N = '0') then
                     next_state <= S_READ;
                  end if;
                  
                  if (IB_DATA(C_IB_TYPE_DATA) = '1' and WR_DST_RDY_N = '0') then
                     next_state <= S_WRITE;
                  end if;
               end if;               
            end if;

            if (IB_DROP = '1' and IB_SOF_N = '0') then
               if (IB_EOF_N = '1') then
                  next_state <= S_DROP;
               end if;
            end if;            

         -- S_WRITE -----------------------------------------------------------
         when  S_WRITE =>
            if (IB_EOF_N = '0' and WR_DST_RDY_N = '0') then
               next_state <= S_ARBITER;
            end if;         

         -- S_READ ------------------------------------------------------------
         when  S_READ =>
            if (IB_EOF_N = '0' and RD_DST_RDY_N = '0') then
               next_state <= S_ARBITER;
            end if;         

         -- S_DROP ------------------------------------------------------------
         when  S_DROP =>
            if (IB_EOF_N = '0') then
               next_state <= S_ARBITER;
            end if;
         
      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state, IB_DATA, IB_SOF_N, IB_EOF_N, IB_SRC_RDY_N, IB_REQ, IB_DROP, RD_DST_RDY_N, WR_DST_RDY_N)
   begin 
      IB_DST_RDY_N <= '1';
      IB_ACK       <= '0';

      RD_SOF_N     <= '1';
      RD_EOF_N     <= '1';
      RD_SRC_RDY_N <= '1';

      WR_SOF_N     <= '1';
      WR_EOF_N     <= '1';
      WR_SRC_RDY_N <= '1';
      WR_DATA      <= IB_DATA;
      
      case (present_state) is 
      
         -- S_ARBITER ---------------------------------------------------------
         when  S_ARBITER => 
            if (IB_REQ = '1' and IB_SOF_N = '0') then            
               if (IB_DATA(C_IB_TYPE_DATA) = '0') then
                  RD_SOF_N     <= IB_SOF_N;
                  RD_EOF_N     <= IB_EOF_N;
                  RD_SRC_RDY_N <= IB_SRC_RDY_N;
                  IB_DST_RDY_N <= RD_DST_RDY_N;
                  
                  IB_ACK       <= not RD_DST_RDY_N;                     
               end if;
               
               if (IB_DATA(C_IB_TYPE_DATA) = '1') then
                  WR_SOF_N     <= IB_SOF_N;
                  WR_EOF_N     <= IB_EOF_N;
                  WR_SRC_RDY_N <= IB_SRC_RDY_N;
                  IB_DST_RDY_N <= WR_DST_RDY_N;
                   
                  IB_ACK       <= not WR_DST_RDY_N;                     
               end if;
            end if;

            if (IB_DROP = '1' and IB_SOF_N = '0') then
               IB_ACK       <= '1';
               IB_DST_RDY_N <= '0';
            end if;                    

         -- S_WRITE -----------------------------------------------------------
         when  S_WRITE =>
            WR_SOF_N     <= IB_SOF_N;
            WR_EOF_N     <= IB_EOF_N;
            WR_SRC_RDY_N <= IB_SRC_RDY_N;
            IB_DST_RDY_N <= WR_DST_RDY_N;

         -- S_READ ------------------------------------------------------------
         when  S_READ =>
            RD_SOF_N     <= IB_SOF_N;
            RD_EOF_N     <= IB_EOF_N;
            RD_SRC_RDY_N <= IB_SRC_RDY_N;
            IB_DST_RDY_N <= RD_DST_RDY_N;         

         -- S_DROP ------------------------------------------------------------
         when  S_DROP =>
            IB_DST_RDY_N <= '0';
         
      end case;                                                                                                   
   end process;                                                                                                   
   
end ib_endpoint_down_fsm_arch;

                     

