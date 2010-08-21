--
-- strict_unit.vhd : IB Endpoint Strict Unit
-- Copyright (C) 2009 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
--               ENTITY DECLARATION -- IB Endpoint Strict Unit               --
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_STRICT_UNIT is
   port (
      -- Common interface -----------------------------------------------------
      CLK           : in std_logic;
      RESET         : in std_logic;
      
      -- Write interface ------------------------------------------------------
      WR_SOF_N      : in  std_logic;
      WR_SRC_RDY_N  : in  std_logic;
      WR_DST_RDY_N  : in  std_logic;
      
      -- IB Read interface ----------------------------------------------------
      IB_SOF_N      : in  std_logic;
      IB_SRC_RDY_N  : in  std_logic;
      IB_DST_RDY_N  : in  std_logic;
      
      -- BM Read interface ----------------------------------------------------
      BM_SOF_N      : in  std_logic;
      BM_SRC_RDY_N  : in  std_logic;
      BM_DST_RDY_N  : in  std_logic;
      BM_WRITE      : in  std_logic;
      
      -- Operation completion interface ---------------------------------------
      WR_COMPLETE   : in  std_logic;
      RD_COMPLETE   : in  std_logic;
      
      -- Output control interface ---------------------------------------------
      WR_EN         : out std_logic;
      RD_EN         : out std_logic
   );
end IB_ENDPOINT_STRICT_UNIT;

-- ----------------------------------------------------------------------------
--           ARCHITECTURE DECLARATION  --  IB Endpoint Strict Unit           --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_strict_unit_arch of IB_ENDPOINT_STRICT_UNIT is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   type   fsm_states is (S_IDLE, S_RD, S_WR, S_WR_RD, S_RD_WR, S_RD_RD,
                         S_RD_RD_WR, S_RD_WR_RD, S_WR_RD_RD);--, S_ERR);
   signal present_state, next_state : fsm_states;
   
   signal wr   : std_logic; -- start of write transaction
   signal ib   : std_logic; -- start of ib read transaction
   signal bm   : std_logic; -- start of bm write trans. (bm write = reading)
   signal wr_c : std_logic; -- write transaction complete
   signal rd_c : std_logic; -- read transaction complete
   
begin
   
   wr <= not (WR_SOF_N or WR_SRC_RDY_N or WR_DST_RDY_N);
   ib <= not (IB_SOF_N or IB_SRC_RDY_N or IB_DST_RDY_N);
   bm <= not (BM_SOF_N or BM_SRC_RDY_N or BM_DST_RDY_N) and BM_WRITE;
   wr_c <= WR_COMPLETE;
   rd_c <= RD_COMPLETE;
   
   -- -------------------------------------------------------------------------
   --                                  FSM                                   --
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
   nextstatelogicp : process(present_state,wr,ib,bm,rd_c,wr_c)
   begin
      next_state <= present_state;
      
      case (present_state) is
         
         -- S_IDLE ----------------------------------------
         when S_IDLE =>
            if (bm = '1' and wr = '1') then
               next_state <= S_RD_WR;
            elsif (ib = '1' or bm = '1') then
               next_state <= S_RD;
            elsif (wr = '1') then
               next_state <= S_WR;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_RD ------------------------------------------
         when S_RD =>
            if (rd_c = '1') then
               if (wr = '1' and (ib = '1' or bm = '1')) then
                  next_state <= S_RD_WR;
               elsif (wr = '1') then
                  next_state <= S_WR;
               elsif (ib = '1' or bm = '1') then
                  next_state <= S_RD;
               else
                  next_state <= S_IDLE;
               end if;
            else
               if (wr = '1' and (ib = '1' or bm = '1')) then
                  next_state <= S_RD_RD_WR;
               elsif (ib = '1' or bm = '1') then
                  next_state <= S_RD_RD;
               elsif (wr = '1') then
                  next_state <= S_RD_WR;
--                elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                            wr_c = '0' and rd_c = '0')) then
--                   next_state <= S_ERR;
               end if;
            end if;

         -- S_RD_WR ----------------------------------------
         when S_RD_WR =>
            if (rd_c = '1' and (ib = '1' or bm = '1')) then
               next_state <= S_WR_RD;
            elsif (rd_c = '1') then
               next_state <= S_WR;
            elsif (ib = '1' or bm = '1') then
               next_state <= S_RD_WR_RD;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_RD_WR_RD -------------------------------------
         when S_RD_WR_RD =>
            if (rd_c = '1') then
               next_state <= S_WR_RD;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_RD_RD ----------------------------------------
         when S_RD_RD =>
            if (rd_c = '1' and wr = '1') then
               next_state <= S_RD_WR;
            elsif (rd_c = '1') then
               next_state <= S_RD;
            elsif (wr = '1') then
               next_state <= S_RD_RD_WR;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_RD_RD_WR -------------------------------------
         when S_RD_RD_WR =>
            if (rd_c = '1') then
               next_state <= S_RD_WR;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_WR -------------------------------------------
         when S_WR =>
            if (wr_c = '1' and bm = '1') then
               next_state <= S_RD;
            elsif (wr_c = '1') then
               next_state <= S_IDLE;
            elsif (bm = '1') then
               next_state <= S_WR_RD;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_WR_RD ----------------------------------------
         when S_WR_RD =>
            if (wr_c = '1' and (ib = '1' or bm = '1')) then
               next_state <= S_RD_RD;
            elsif (wr_c = '1') then
               next_state <= S_RD;
            elsif (ib = '1' or bm = '1') then
               next_state <= S_WR_RD_RD;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         -- S_WR_RD_RD -------------------------------------
         when S_WR_RD_RD =>
            if (wr_c = '1') then
               next_state <= S_RD_RD;
--             elsif (not (wr = '0' and ib = '0' and bm = '0' and
--                         wr_c = '0' and rd_c = '0')) then
--                next_state <= S_ERR;
            end if;
         
         
--          when S_ERR =>
         
      end case;
   end process;
   
   -- output logic ------------------------------------------------------------
   outputlogicp : process(present_state,wr,ib,bm,rd_c,wr_c)
   begin
      wr_en <= '0';
      rd_en <= '0';
      
      case (present_state) is
         
         -- S_IDLE ----------------------------------------
         when S_IDLE =>
            
         -- S_RD ------------------------------------------
         when S_RD =>
            rd_en <= '1';
         
         -- S_RD_WR ----------------------------------------
         when S_RD_WR =>
            rd_en <= '1';
         
         -- S_RD_WR_RD -------------------------------------
         when S_RD_WR_RD =>
            rd_en <= '1';
         
         -- S_RD_RD ----------------------------------------
         when S_RD_RD =>
            rd_en <= '1';
         
         -- S_RD_RD_WR -------------------------------------
         when S_RD_RD_WR =>
            rd_en <= '1';
         
         -- S_WR -------------------------------------------
         when S_WR =>
            wr_en <= '1';
         
         -- S_WR_RD ----------------------------------------
         when S_WR_RD =>
            wr_en <= '1';
         
         -- S_WR_RD_RD -------------------------------------
         when S_WR_RD_RD =>
            wr_en <= '1';
         
--          when S_ERR =>
--             wr_en <= 'X';
--             rd_en <= 'X';
         
      end case;
   end process;
   
end ib_endpoint_strict_unit_arch;

