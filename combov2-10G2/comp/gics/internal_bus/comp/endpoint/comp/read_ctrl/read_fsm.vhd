--
-- read_fsm.vhd : IB Endpoint Read FSM
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
--                 ENTITY DECLARATION -- IB Endpoint Read FSM                -- 
-- ----------------------------------------------------------------------------

entity GICS_IB_ENDPOINT_READ_FSM is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH     : integer := 64;
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE      : t_ibrd_type := CONTINUAL      
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  
 
      -- IB interface ---------------------------------------------------------
      IB_SOF_N       : in  std_logic;
      IB_EOF_N       : in  std_logic;
      IB_SRC_RDY_N   : in  std_logic;
      IB_DST_RDY_N   : out std_logic;

      -- RD interface ---------------------------------------------------------
      RD_SOF         : out std_logic;
      RD_EOF         : out std_logic;
      RD_REQ         : out std_logic;
      RD_ARDY_ACCEPT : in  std_logic;

      -- Control interface ----------------------------------------------------
      COUNT          : in  std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0); 
      HEADER_LAST    : in std_logic;
      HBUF_FULL      : in std_logic;
      HBUF_WE        : out std_logic;
      COUNT_CE       : out std_logic;
      ADDR_CE        : out std_logic;
      
      -- Strict unit interface ------------------------------------------------
      RD_EN          : in  std_logic
   );
end GICS_IB_ENDPOINT_READ_FSM;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  IB Endpoint Read FSM           --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_read_fsm_arch of GICS_IB_ENDPOINT_READ_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_HEADER, S_SOF, S_INC);
   signal present_state, next_state : fsm_states; 
   
begin

   -- -------------------------------------------------------------------------                                                         
   --                               READ FSM                                 --                                                         
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
   nextstatelogicp : process(present_state, IB_SOF_N, IB_EOF_N, IB_SRC_RDY_N, 
                          RD_ARDY_ACCEPT, COUNT, HEADER_LAST, HBUF_FULL, RD_EN) 
   begin                                                                                                          
      next_state <= present_state;                                                                                
                                                                                                                  
      case (present_state) is                                                                                                               

         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            if (HEADER_LAST = '1' and HBUF_FULL = '0') then
               next_state <= S_SOF;
            end if;

         -- S_SOF -----------------------------------------
         when  S_SOF =>
            if (READ_TYPE = CONTINUAL) then
               if (COUNT = 1 and RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  if (HEADER_LAST = '1' and HBUF_FULL = '0') then
                     next_state <= S_SOF;
                  else
                     next_state <= S_HEADER;
                  end if;
               elsif (RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  next_state <= S_INC;
               end if;
            end if;

            if (READ_TYPE = PACKET) then
               if (RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  if (HEADER_LAST = '1' and HBUF_FULL = '0') then
                     next_state <= S_SOF;
                  else
                     next_state <= S_HEADER;
                  end if;
               end if;
            end if;            

         -- S_INC -----------------------------------------
         when  S_INC =>
               if (COUNT = 1 and RD_ARDY_ACCEPT = '1') then
                  if (HEADER_LAST = '1' and HBUF_FULL = '0') then
                     next_state <= S_SOF;
                  else
                     next_state <= S_HEADER;
                  end if;                  
               end if;

      end case;                                                                                                    
   end process;                                                                                                    
                                                                                                                         
   -- output logic ------------------------------------------------------------                                                                                                 
   outputlogicp : process(present_state, IB_SOF_N, IB_EOF_N, IB_SRC_RDY_N, 
                          RD_ARDY_ACCEPT, COUNT, HEADER_LAST, HBUF_FULL, RD_EN)
   begin 
      IB_DST_RDY_N <= '1';
      RD_SOF       <= '0';
      RD_EOF       <= '0';
      RD_REQ       <= '0';
      HBUF_WE      <= '0';
      COUNT_CE     <= '0';
      ADDR_CE      <= '0';
                   
      case (present_state) is 
 
         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            IB_DST_RDY_N <= HBUF_FULL;

         -- S_SOF -----------------------------------------
         when  S_SOF =>
            RD_SOF <= '1';
            RD_REQ <= RD_EN;
         
            if (READ_TYPE = CONTINUAL) then
               if (COUNT = 1 and RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  IB_DST_RDY_N <= HBUF_FULL;
                  RD_EOF       <= '1';
                  HBUF_WE      <= '1';
                  
               elsif (RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  HBUF_WE      <= '1';
                  COUNT_CE     <= '1';
                  ADDR_CE      <= '1';
               end if;
            end if;

            if (READ_TYPE = PACKET) then
               RD_EOF <= '1';
               
               if (RD_ARDY_ACCEPT = '1' and RD_EN = '1') then
                  IB_DST_RDY_N <= HBUF_FULL;
                  HBUF_WE      <= '1';
               end if;
           end if;            

         -- S_INC -----------------------------------------
         when  S_INC =>
               RD_REQ <= '1';
         
               if (COUNT = 1 and RD_ARDY_ACCEPT = '1') then
                  IB_DST_RDY_N <= HBUF_FULL;
                  RD_EOF       <= '1';
               elsif (RD_ARDY_ACCEPT = '1') then
                  COUNT_CE     <= '1';
                  ADDR_CE      <= '1';                              
               end if; 
         
      end case;                                                                                                   
   end process;                                                                                                   
   
end ib_endpoint_read_fsm_arch;



