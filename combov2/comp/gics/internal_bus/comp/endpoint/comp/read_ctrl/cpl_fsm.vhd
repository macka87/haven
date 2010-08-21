--
-- cpl_fsm.vhd : IB Endpoint Completion FSM
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
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--              ENTITY DECLARATION -- IB Endpoint Completion FSM             -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_CPL_FSM is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH     : integer := 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- Header interface -----------------------------------------------------
      HEADER_SOF     : in  std_logic;
      HEADER_EOF     : in  std_logic;
      HEADER_SRC_RDY : in  std_logic;
      HEADER_DST_RDY : out std_logic;

      -- Data Interface -------------------------------------------------------
      DATA_SOF       : in  std_logic;
      DATA_EOF       : in  std_logic;
      DATA_SRC_RDY   : in  std_logic;
      DATA_DST_RDY   : out std_logic;

      -- IB Interface ---------------------------------------------------------
      IB_SOF_N       : out std_logic;
      IB_EOF_N       : out std_logic;
      IB_SRC_RDY_N   : out std_logic;
      IB_DST_RDY_N   : in  std_logic
   );
end IB_ENDPOINT_CPL_FSM;

-- ----------------------------------------------------------------------------
--          ARCHITECTURE DECLARATION  --  IB Endpoint Completion FSM         --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_cpl_fsm_arch of IB_ENDPOINT_CPL_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_HEADER, S_DATA);
   signal present_state, next_state : fsm_states; 
   
begin

   -- -------------------------------------------------------------------------                                                         
   --                            COMPLETION FSM                              --  
   -- -------------------------------------------------------------------------                                                     
                                                                                                                                    
   -- synchronize logic -------------------------------------------------------                                   
   synchlogp : process(CLK)                                                                                       
   begin                                                                                                          
      if (CLK'event and CLK = '1') then                                                                           
         if (RESET = '1') then                                                                                           
            present_state <= S_HEADER; 
         else      
            present_state <= next_state;
         end if;
      end if;                                                                                                  
   end process;                                                                                                

   -- next state logic --------------------------------------------------------                                                                                           
   nextstatelogicp : process(present_state, DATA_EOF, HEADER_EOF, IB_DST_RDY_N) 
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               

         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            if (HEADER_EOF = '1' and IB_DST_RDY_N = '0') then
               next_state <= S_DATA;
            end if;

         -- S_DATA ----------------------------------------
         when  S_DATA =>
            if (DATA_EOF = '1' and IB_DST_RDY_N = '0') then
               next_state <= S_HEADER;
            end if;

      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state, DATA_SOF, DATA_EOF, DATA_SRC_RDY, IB_DST_RDY_N,
                                         HEADER_SOF, HEADER_EOF, HEADER_SRC_RDY)
   begin        
      DATA_DST_RDY   <= '0';
      HEADER_DST_RDY <= '0';      
      IB_SOF_N       <= '1';
      IB_EOF_N       <= '1';
      IB_SRC_RDY_N   <= '1';
                              
      case (present_state) is 
 
         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            IB_SOF_N       <= not HEADER_SOF;
            IB_SRC_RDY_N   <= not HEADER_SRC_RDY;
            HEADER_DST_RDY <= not IB_DST_RDY_N;            

         -- S_DATA ----------------------------------------
         when  S_DATA =>
            IB_EOF_N       <= not DATA_EOF;
            IB_SRC_RDY_N   <= not DATA_SRC_RDY;
            DATA_DST_RDY   <= not IB_DST_RDY_N;                   
        
      end case;                                                                                                   
   end process;                                                                                                   
   
end ib_endpoint_cpl_fsm_arch;



