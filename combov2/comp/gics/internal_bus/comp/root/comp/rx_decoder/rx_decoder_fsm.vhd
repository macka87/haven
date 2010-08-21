--
-- pcie_rx_decoder_fsm.vhd : PCI-e RX decoder fsm
-- Copyright (C) 2008 CESNET
-- Author(s): Petr Kobierský <kobierskyk@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity PCIE_RX_DECODER_FSM is
  port (
    -- PCI Express Common signals -------------------------------------------
      TRN_RESET_N           : in  std_logic; 
      TRN_CLK               : in  std_logic; 
    -- PCI Express RX interface ---------------------------------------------
      TRN_RSOF_N            : in  std_logic;                       -- Start-of-Frame (SOF)
      TRN_REOF_N            : in  std_logic;                       -- End-of-Frame (EOF)
      TRN_RSRC_RDY_N        : in  std_logic;                       -- Source Ready
      TRN_RDST_RDY_N        : out std_logic;                       -- Destination Ready
      TRN_RERRFWD_N         : in  std_logic;                       -- Error Forward (Asserted by the core for entire packet - remove packet)
   -- Control signals from datapath ----------------------------------------
      REG_NO_DATA           : in  std_logic;                       -- Transaction with no data (read request)
      REG_3DW               : in  std_logic;                       -- Transaction in 3DW format
      REG_SHIFT32           : in  std_logic;                       -- Reg shift 32
      UNSUPPORTED           : in  std_logic;                       -- Decoded type (read, write, completition)
      LAST_DATA             : in  std_logic;                       -- Last data signal (escape from data generation)
      DATA_VLD              : in  std_logic;
   -- Control signals for datapath -----------------------------------------
      GEN_HDR0              : out std_logic;
      GEN_HDR1              : out std_logic;
      FSM_CONTROL_WE        : out std_logic;                       -- Control signal for storing 3DW and NO_DATA registers
      PIPE_REG_WE           : out std_logic;                       -- Enable write to pipeline
   -- IB Generator interface ---------------------------------------------
      SOP_N                 : out std_logic;                       -- Start of Packet
      EOP_N                 : out std_logic;                       -- End of Packet
      SRC_RDY_N             : out std_logic;                       -- Source Ready
      DST_RDY_N             : in  std_logic                        -- Destination Ready
    );
end PCIE_RX_DECODER_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_RX_DECODER_FSM is


   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
  
   -- Control FSM declaration
   type   t_states is (st_idle, st_drop, st_hdr0, st_hdr1, st_data);
   signal present_state, next_state : t_states;


   
begin


-- SWITCH INPUT FSM -----------------------------------------------------------
-- next state clk logic
clk_d: process(TRN_CLK, TRN_RESET_N)
  begin
    if (TRN_CLK='1' and TRN_CLK'event) then
      if TRN_RESET_N = '0' then
        present_state <= st_idle;
      else
        present_state <= next_state;
      end if;
    end if;
  end process;


 
-- next state logic
state_trans: process(present_state, TRN_RSOF_N, TRN_REOF_N, TRN_RSRC_RDY_N,
                     TRN_RERRFWD_N, UNSUPPORTED, DST_RDY_N, REG_NO_DATA,
                     REG_3DW, LAST_DATA)
  begin
    case present_state is

      -- ST_IDLE (OKI)
      when st_idle =>
        -- There is a valid frame on a input
        if (TRN_RSOF_N = '0' and TRN_RSRC_RDY_N = '0') then
          if (UNSUPPORTED = '1' or TRN_RERRFWD_N = '0') then -- Unknown unsupported transaction
            next_state <= st_drop; -- Go for transaction drop
          else
            next_state <= st_hdr0; -- Go for hdr0 generation
          end if;
        else
          next_state <= st_idle; -- Wait for valid frame
        end if;

      -- ST_DROP (OKI)
      when st_drop =>
        if (TRN_REOF_N = '0' and TRN_RSRC_RDY_N = '0') then
          next_state <= st_idle;
        else
          next_state <= st_drop;
        end if;
        

      -- ST_HDR0 (OKI)
      when st_hdr0 => -- Generate hdr1 if dst and src is ready
        if (TRN_RSRC_RDY_N = '0' and DST_RDY_N = '0') then
          next_state <= st_hdr1; -- Go for hdr1 generation
        else
          next_state <= st_hdr0; -- Wait for data ready
        end if;


      -- ST_HDR1 =>
      when st_hdr1 =>
        if (DST_RDY_N = '0') then
          if (REG_NO_DATA='1') then
            if (TRN_RSOF_N = '0' and TRN_RSRC_RDY_N = '0') then
              if (UNSUPPORTED = '1' or TRN_RERRFWD_N = '0') then -- Unknown unsupported transaction
                next_state <= st_drop; -- Go for transaction drop
              else
                next_state <= st_hdr0;      -- Go for hdr0 processing
              end if;
            else
              next_state <= st_idle;      -- Go to Idle state
            end if;            
          else
            next_state <= st_data;
          end if;
        else
          next_state <= st_hdr1;
        end if;

      -- ST_DATA (OKI)
      when st_data =>
        if (LAST_DATA = '1' and DST_RDY_N = '0' and TRN_RSOF_N = '0' and TRN_RSRC_RDY_N = '0') then
          if (UNSUPPORTED = '1' or TRN_RERRFWD_N = '0') then -- Unknown unsupported transaction
            next_state <= st_drop; -- Go for transaction drop
          else
            next_state <= st_hdr0;      -- Go for hdr0 processing
          end if;
        elsif (LAST_DATA = '1' and DST_RDY_N = '0') then
          next_state <= st_idle;
        else
          next_state <= st_data;
        end if;

      end case;


  end process;

-- output logic
output_logic: process(present_state, TRN_REOF_N, TRN_RSRC_RDY_N,
                      DST_RDY_N, REG_NO_DATA, REG_3DW, REG_SHIFT32, LAST_DATA, DATA_VLD)
  begin
   
   TRN_RDST_RDY_N      <= '1';
   SOP_N               <= '1';
   EOP_N               <= '1';
   SRC_RDY_N           <= '1';
   FSM_CONTROL_WE      <= '0';
   GEN_HDR0            <= '0';
   GEN_HDR1            <= '0';
   PIPE_REG_WE         <= '0';
   
   case present_state is

      -- ST_IDLE (OKI)
      when st_idle =>
        TRN_RDST_RDY_N      <= '0';
        PIPE_REG_WE         <= '1';

      -- ST_DROP (OKI)
      when st_drop =>
        TRN_RDST_RDY_N      <= '0';

      -- ST_HDR0 (OKI)
      when st_hdr0 =>
        GEN_HDR0            <= '1';
        FSM_CONTROL_WE      <= '1';
        SOP_N               <= '0';
        SRC_RDY_N           <= TRN_RSRC_RDY_N;
        TRN_RDST_RDY_N      <= DST_RDY_N;
        PIPE_REG_WE         <= not DST_RDY_N;

      -- ST_HDR1
      when st_hdr1 =>
        GEN_HDR1            <= '1';
        SRC_RDY_N           <= '0';
        EOP_N               <= not REG_NO_DATA;
        PIPE_REG_WE         <= (not REG_SHIFT32 and not REG_3DW and not DST_RDY_N) or (REG_NO_DATA and not DST_RDY_N);
        TRN_RDST_RDY_N      <= not ((not REG_SHIFT32 and not REG_3DW and not DST_RDY_N) or (REG_NO_DATA and not DST_RDY_N));

      -- ST_DATA
      when st_data =>
        SRC_RDY_N           <= not DATA_VLD;
        PIPE_REG_WE         <= not DST_RDY_N;
        TRN_RDST_RDY_N      <= DST_RDY_N;
        EOP_N               <= not LAST_DATA;
  

      end case;
  end process;



end architecture FULL;

