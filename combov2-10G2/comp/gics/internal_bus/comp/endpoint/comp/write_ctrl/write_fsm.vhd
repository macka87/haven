--
-- write_fsm.vhd : IB Endpoint Write FSM
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
--                 ENTITY DECLARATION -- IB Endpoint Write FSM               --
-- ----------------------------------------------------------------------------

entity GICS_IB_ENDPOINT_WRITE_FSM is
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  
 
      -- IB interface ---------------------------------------------------------
      IB_SOF_N     : in  std_logic;
      IB_EOF_N     : in  std_logic;
      IB_SRC_RDY_N : in  std_logic;
      IB_DST_RDY_N : out std_logic;

      -- WR interface ---------------------------------------------------------
      WR_SOF       : out std_logic;
      WR_EOF       : out std_logic;
      WR_REQ       : out std_logic;
      WR_RDY       : in  std_logic;

      -- Control interface ----------------------------------------------------
      HEADER_LAST  : in  std_logic;
      HEADER       : out std_logic;
      ADDR_CE      : out std_logic;
      
      -- Strict unit interface ------------------------------------------------
      WR_EN        : in  std_logic
   );
end GICS_IB_ENDPOINT_WRITE_FSM;

-- ----------------------------------------------------------------------------
--             ARCHITECTURE DECLARATION  --  IB Endpoint Write FSM           --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_write_fsm_arch of GICS_IB_ENDPOINT_WRITE_FSM is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   type   fsm_states is (S_HEADER, S_SOF, S_DATA);
   signal present_state, next_state : fsm_states; 
   
begin

   -- -------------------------------------------------------------------------
   --                               WRITE FSM                                --
   -- -------------------------------------------------------------------------
   
   -- synchronize logic -------------------------------------------------------
   synchlogp : process(RESET, CLK)
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
   nextstatelogicp : process(present_state, IB_EOF_N, IB_SRC_RDY_N, WR_RDY,
                             HEADER_LAST, WR_EN) 
   begin
      next_state <= present_state;
      
      case (present_state) is

         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            if (HEADER_LAST = '1') then
               next_state <= S_SOF;
            end if;

         -- S_SOF -----------------------------------------
         when  S_SOF =>
            if (IB_SRC_RDY_N = '0' and WR_RDY = '1' and WR_EN = '1') then
               if (IB_EOF_N = '0') then
                  next_state <= S_HEADER;
               else
                  next_state <= S_DATA;
               end if;
            end if;

         -- S_DATA ----------------------------------------
         when  S_DATA =>
            if (IB_EOF_N = '0' and WR_RDY = '1') then
               next_state <= S_HEADER;
            end if;

      end case;
   end process;
   
   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state, IB_EOF_N, IB_SRC_RDY_N, WR_RDY,
                          HEADER_LAST, WR_EN)
   begin 
      IB_DST_RDY_N <= '1';
      WR_SOF       <= '0';
      WR_EOF       <= '0';
      WR_REQ       <= '0';
      ADDR_CE      <= '0';
      HEADER       <= '0';
      
      case (present_state) is 
 
         -- S_HEADER --------------------------------------
         when  S_HEADER =>
            IB_DST_RDY_N <= '0';
            HEADER       <= '1';

         -- S_SOF -----------------------------------------
         when  S_SOF =>
            IB_DST_RDY_N <= not (WR_RDY and WR_EN);
            WR_SOF       <= not IB_SRC_RDY_N;
            WR_EOF       <= not IB_EOF_N;
            WR_REQ       <= not IB_SRC_RDY_N and WR_EN;
            
            if (IB_SRC_RDY_N = '0' and WR_RDY = '1' and WR_EN = '1') then
               ADDR_CE <= '1';
            end if;

         -- S_DATA ----------------------------------------
         when  S_DATA =>
            IB_DST_RDY_N <= not WR_RDY;
            WR_EOF       <= not IB_EOF_N;
            WR_REQ       <= not IB_SRC_RDY_N;
            
            if (IB_SRC_RDY_N = '0' and WR_RDY = '1') then
               ADDR_CE <= '1';
            end if;
            
      end case;
   end process;
   
end ib_endpoint_write_fsm_arch;

